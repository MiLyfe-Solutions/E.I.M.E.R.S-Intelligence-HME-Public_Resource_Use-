import V185TrunkScan20Chunk066

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_407517 : List Nat := [1, 4, 3, 1, 3, 2, 2, 4]
def baseStart_407517 : Nat := 118140960795 + 407517 * 2 ^ 59
def prefixEnd_407517 : Nat := 4983230072969 + 3 ^ 40 * 407517 * 2
def baseEnd_407517 : Nat := 62000621001003650833591

theorem tailTrace_407517 : CollatzResearch.WordTrace tailWord_407517 prefixEnd_407517 62000621001003650833591 := by
  unfold tailWord_407517
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863366064642982207700805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9908910709761988138467203 14863366064642982207700805)
  ·
    refine ⟨2786881137120559163943901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14863366064642982207700805 2786881137120559163943901)
    ·
      refine ⟨1045080426420209686478963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2786881137120559163943901 1045080426420209686478963)
      ·
        refine ⟨1567620639630314529718445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045080426420209686478963 1567620639630314529718445)
        ·
          refine ⟨587857739861367948644417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1567620639630314529718445 587857739861367948644417)
          ·
            refine ⟨440893304896025961483313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587857739861367948644417 440893304896025961483313)
            ·
              refine ⟨330669978672019471112485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440893304896025961483313 330669978672019471112485)
              ·
                refine ⟨62000621001003650833591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330669978672019471112485 62000621001003650833591)
                ·
                  rfl

theorem cell20_407517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_407517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407517 prefixEnd_407517 := by exact prefixLift 407517
  have htrace : WordTrace (prefixWord ++ tailWord_407517) baseStart_407517 baseEnd_407517 := by
    simpa [prefixWord, tailWord_407517, baseEnd_407517] using wordTrace_append hprefix tailTrace_407517
  have hstable : (prefixWord ++ tailWord_407517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407517).length < 2 ^ (prefixWord ++ tailWord_407517).sum := by decide
  have hdescent : baseEnd_407517 < baseStart_407517 := by decide
  rcases family_descends (prefixWord ++ tailWord_407517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407521 : List Nat := [1, 2, 3, 1, 2, 1, 6, 4]
def baseStart_407521 : Nat := 118140960795 + 407521 * 2 ^ 59
def prefixEnd_407521 : Nat := 4983230072969 + 3 ^ 40 * 407521 * 2
def baseEnd_407521 : Nat := 62001229570668238789141

theorem tailTrace_407521 : CollatzResearch.WordTrace tailWord_407521 prefixEnd_407521 62001229570668238789141 := by
  unfold tailWord_407521
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863511956628490890846417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9909007971085660593897611 14863511956628490890846417)
  ·
    refine ⟨11147633967471368168134813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14863511956628490890846417 11147633967471368168134813)
    ·
      refine ⟨4180362737801763063050555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11147633967471368168134813 4180362737801763063050555)
      ·
        refine ⟨6270544106702644594575833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180362737801763063050555 6270544106702644594575833)
        ·
          refine ⟨4702908080026983445931875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6270544106702644594575833 4702908080026983445931875)
          ·
            refine ⟨7054362120040475168897813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4702908080026983445931875 7054362120040475168897813)
            ·
              refine ⟨330673224376897273542085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7054362120040475168897813 330673224376897273542085)
              ·
                refine ⟨62001229570668238789141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330673224376897273542085 62001229570668238789141)
                ·
                  rfl

theorem cell20_407521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_407521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407521 prefixEnd_407521 := by exact prefixLift 407521
  have htrace : WordTrace (prefixWord ++ tailWord_407521) baseStart_407521 baseEnd_407521 := by
    simpa [prefixWord, tailWord_407521, baseEnd_407521] using wordTrace_append hprefix tailTrace_407521
  have hstable : (prefixWord ++ tailWord_407521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407521).length < 2 ^ (prefixWord ++ tailWord_407521).sum := by decide
  have hdescent : baseEnd_407521 < baseStart_407521 := by decide
  rcases family_descends (prefixWord ++ tailWord_407521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407527 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 2]
def baseStart_407527 : Nat := 118140960795 + 407527 * 2 ^ 59
def prefixEnd_407527 : Nat := 4983230072969 + 3 ^ 40 * 407527 * 2
def baseEnd_407527 : Nat := 186006427275495362167399

theorem tailTrace_407527 : CollatzResearch.WordTrace tailWord_407527 prefixEnd_407527 186006427275495362167399 := by
  unfold tailWord_407527
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863730794606753915564835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9909153863071169277043223 14863730794606753915564835)
  ·
    refine ⟨22295596191910130873347253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14863730794606753915564835 22295596191910130873347253)
    ·
      refine ⟨2090212142991574769376305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22295596191910130873347253 2090212142991574769376305)
      ·
        refine ⟨1567659107243681077032229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2090212142991574769376305 1567659107243681077032229)
        ·
          refine ⟨293936082608190201943543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1567659107243681077032229 293936082608190201943543)
          ·
            refine ⟨440904123912285302915315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293936082608190201943543 440904123912285302915315)
            ·
              refine ⟨661356185868427954372973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440904123912285302915315 661356185868427954372973)
              ·
                refine ⟨248008569700660482889865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 661356185868427954372973 248008569700660482889865)
                ·
                  refine ⟨186006427275495362167399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248008569700660482889865 186006427275495362167399)
                  ·
                    rfl

theorem cell20_407527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 2].length) (baseStart_407527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407527 prefixEnd_407527 := by exact prefixLift 407527
  have htrace : WordTrace (prefixWord ++ tailWord_407527) baseStart_407527 baseEnd_407527 := by
    simpa [prefixWord, tailWord_407527, baseEnd_407527] using wordTrace_append hprefix tailTrace_407527
  have hstable : (prefixWord ++ tailWord_407527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407527).length < 2 ^ (prefixWord ++ tailWord_407527).sum := by decide
  have hdescent : baseEnd_407527 < baseStart_407527 := by decide
  rcases family_descends (prefixWord ++ tailWord_407527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407559 : List Nat := [1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_407559 : Nat := 118140960795 + 407559 * 2 ^ 59
def prefixEnd_407559 : Nat := 4983230072969 + 3 ^ 40 * 407559 * 2
def baseEnd_407559 : Nat := 62007010982481824366867

theorem tailTrace_407559 : CollatzResearch.WordTrace tailWord_407559 prefixEnd_407559 62007010982481824366867 := by
  unfold tailWord_407559
  simp only [CollatzResearch.WordTrace]
  refine ⟨14864897930490823380729731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9909931953660548920486487 14864897930490823380729731)
  ·
    refine ⟨22297346895736235071094597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14864897930490823380729731 22297346895736235071094597)
    ·
      refine ⟨4180752542950544075830237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22297346895736235071094597 4180752542950544075830237)
      ·
        refine ⟨1567782203606454028436339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4180752542950544075830237 1567782203606454028436339)
        ·
          refine ⟨2351673305409681042654509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567782203606454028436339 2351673305409681042654509)
          ·
            refine ⟨881877489528630390995441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2351673305409681042654509 881877489528630390995441)
            ·
              refine ⟨661408117146472793246581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881877489528630390995441 661408117146472793246581)
              ·
                refine ⟨62007010982481824366867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 661408117146472793246581 62007010982481824366867)
                ·
                  rfl

theorem cell20_407559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_407559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407559 prefixEnd_407559 := by exact prefixLift 407559
  have htrace : WordTrace (prefixWord ++ tailWord_407559) baseStart_407559 baseEnd_407559 := by
    simpa [prefixWord, tailWord_407559, baseEnd_407559] using wordTrace_append hprefix tailTrace_407559
  have hstable : (prefixWord ++ tailWord_407559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407559).length < 2 ^ (prefixWord ++ tailWord_407559).sum := by decide
  have hdescent : baseEnd_407559 < baseStart_407559 := by decide
  rcases family_descends (prefixWord ++ tailWord_407559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407607 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 2]
def baseStart_407607 : Nat := 118140960795 + 407607 * 2 ^ 59
def prefixEnd_407607 : Nat := 4983230072969 + 3 ^ 40 * 407607 * 2
def baseEnd_407607 : Nat := 186042941455370639500405

theorem tailTrace_407607 : CollatzResearch.WordTrace tailWord_407607 prefixEnd_407607 186042941455370639500405 := by
  unfold tailWord_407607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14866648634316927578477075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9911099089544618385651383 14866648634316927578477075)
  ·
    refine ⟨22299972951475391367715613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14866648634316927578477075 22299972951475391367715613)
    ·
      refine ⟨8362489856803271762893355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22299972951475391367715613 8362489856803271762893355)
      ·
        refine ⟨12543734785204907644340033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8362489856803271762893355 12543734785204907644340033)
        ·
          refine ⟨9407801088903680733255025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12543734785204907644340033 9407801088903680733255025)
          ·
            refine ⟨7055850816677760549941269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9407801088903680733255025 7055850816677760549941269)
            ·
              refine ⟨330743007031770025778497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7055850816677760549941269 330743007031770025778497)
              ·
                refine ⟨248057255273827519333873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330743007031770025778497 248057255273827519333873)
                ·
                  refine ⟨186042941455370639500405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248057255273827519333873 186042941455370639500405)
                  ·
                    rfl

theorem cell20_407607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 2].length) (baseStart_407607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407607 prefixEnd_407607 := by exact prefixLift 407607
  have htrace : WordTrace (prefixWord ++ tailWord_407607) baseStart_407607 baseEnd_407607 := by
    simpa [prefixWord, tailWord_407607, baseEnd_407607] using wordTrace_append hprefix tailTrace_407607
  have hstable : (prefixWord ++ tailWord_407607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407607).length < 2 ^ (prefixWord ++ tailWord_407607).sum := by decide
  have hdescent : baseEnd_407607 < baseStart_407607 := by decide
  rcases family_descends (prefixWord ++ tailWord_407607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407666 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_407666 : Nat := 118140960795 + 407666 * 2 ^ 59
def prefixEnd_407666 : Nat := 4983230072969 + 3 ^ 40 * 407666 * 2
def baseEnd_407666 : Nat := 186069870663028656533497

theorem tailTrace_407666 : CollatzResearch.WordTrace tailWord_407666 prefixEnd_407666 186069870663028656533497 := by
  unfold tailWord_407666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717200135275795163718713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9912533694068787103249901 3717200135275795163718713)
  ·
    refine ⟨2787900101456846372789035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3717200135275795163718713 2787900101456846372789035)
    ·
      refine ⟨4181850152185269559183553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2787900101456846372789035 4181850152185269559183553)
      ·
        refine ⟨3136387614138952169387665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4181850152185269559183553 3136387614138952169387665)
        ·
          refine ⟨2352290710604214127040749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136387614138952169387665 2352290710604214127040749)
          ·
            refine ⟨882109016476580297640281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2352290710604214127040749 882109016476580297640281)
            ·
              refine ⟨661581762357435223230211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882109016476580297640281 661581762357435223230211)
              ·
                refine ⟨992372643536152834845317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661581762357435223230211 992372643536152834845317)
                ·
                  refine ⟨186069870663028656533497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992372643536152834845317 186069870663028656533497)
                  ·
                    rfl

theorem cell20_407666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_407666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407666 prefixEnd_407666 := by exact prefixLift 407666
  have htrace : WordTrace (prefixWord ++ tailWord_407666) baseStart_407666 baseEnd_407666 := by
    simpa [prefixWord, tailWord_407666, baseEnd_407666] using wordTrace_append hprefix tailTrace_407666
  have hstable : (prefixWord ++ tailWord_407666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407666).length < 2 ^ (prefixWord ++ tailWord_407666).sum := by decide
  have hdescent : baseEnd_407666 < baseStart_407666 := by decide
  rcases family_descends (prefixWord ++ tailWord_407666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407687 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_407687 : Nat := 118140960795 + 407687 * 2 ^ 59
def prefixEnd_407687 : Nat := 4983230072969 + 3 ^ 40 * 407687 * 2
def baseEnd_407687 : Nat := 186079455635245916833411

theorem tailTrace_407687 : CollatzResearch.WordTrace tailWord_407687 prefixEnd_407687 186079455635245916833411 := by
  unfold tailWord_407687
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869566474027101241389315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9913044316018067494259543 14869566474027101241389315)
  ·
    refine ⟨22304349711040651862083973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14869566474027101241389315 22304349711040651862083973)
    ·
      refine ⟨4182065570820122224140745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22304349711040651862083973 4182065570820122224140745)
      ·
        refine ⟨3136549178115091668105559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4182065570820122224140745 3136549178115091668105559)
        ·
          refine ⟨4704823767172637502158339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136549178115091668105559 4704823767172637502158339)
          ·
            refine ⟨7057235650758956253237509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4704823767172637502158339 7057235650758956253237509)
            ·
              refine ⟨1323231684517304297482033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7057235650758956253237509 1323231684517304297482033)
              ·
                refine ⟨992423763387978223111525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323231684517304297482033 992423763387978223111525)
                ·
                  refine ⟨186079455635245916833411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992423763387978223111525 186079455635245916833411)
                  ·
                    rfl

theorem cell20_407687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_407687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407687 prefixEnd_407687 := by exact prefixLift 407687
  have htrace : WordTrace (prefixWord ++ tailWord_407687) baseStart_407687 baseEnd_407687 := by
    simpa [prefixWord, tailWord_407687, baseEnd_407687] using wordTrace_append hprefix tailTrace_407687
  have hstable : (prefixWord ++ tailWord_407687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407687).length < 2 ^ (prefixWord ++ tailWord_407687).sum := by decide
  have hdescent : baseEnd_407687 < baseStart_407687 := by decide
  rcases family_descends (prefixWord ++ tailWord_407687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407690 : List Nat := [3, 1, 2, 3, 1, 4, 2, 4]
def baseStart_407690 : Nat := 118140960795 + 407690 * 2 ^ 59
def prefixEnd_407690 : Nat := 4983230072969 + 3 ^ 40 * 407690 * 2
def baseEnd_407690 : Nat := 62026941638997079911133

theorem tailTrace_407690 : CollatzResearch.WordTrace tailWord_407690 prefixEnd_407690 62026941638997079911133 := by
  unfold tailWord_407690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717418973254058188437131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9913117262010821835832349 3717418973254058188437131)
  ·
    refine ⟨5576128459881087282655697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3717418973254058188437131 5576128459881087282655697)
    ·
      refine ⟨4182096344910815461991773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5576128459881087282655697 4182096344910815461991773)
      ·
        refine ⟨1568286129341555798246915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4182096344910815461991773 1568286129341555798246915)
        ·
          refine ⟨2352429194012333697370373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568286129341555798246915 2352429194012333697370373)
          ·
            refine ⟨441080473877312568256945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2352429194012333697370373 441080473877312568256945)
            ·
              refine ⟨330810355407984426192709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441080473877312568256945 330810355407984426192709)
              ·
                refine ⟨62026941638997079911133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330810355407984426192709 62026941638997079911133)
                ·
                  rfl

theorem cell20_407690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_407690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407690 prefixEnd_407690 := by exact prefixLift 407690
  have htrace : WordTrace (prefixWord ++ tailWord_407690) baseStart_407690 baseEnd_407690 := by
    simpa [prefixWord, tailWord_407690, baseEnd_407690] using wordTrace_append hprefix tailTrace_407690
  have hstable : (prefixWord ++ tailWord_407690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407690).length < 2 ^ (prefixWord ++ tailWord_407690).sum := by decide
  have hdescent : baseEnd_407690 < baseStart_407690 := by decide
  rcases family_descends (prefixWord ++ tailWord_407690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407701 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_407701 : Nat := 118140960795 + 407701 * 2 ^ 59
def prefixEnd_407701 : Nat := 4983230072969 + 3 ^ 40 * 407701 * 2
def baseEnd_407701 : Nat := 186085845616724090366687

theorem tailTrace_407701 : CollatzResearch.WordTrace tailWord_407701 prefixEnd_407701 186085845616724090366687 := by
  unfold tailWord_407701
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870077095976381632398957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9913384730650921088265971 14870077095976381632398957)
  ·
    refine ⟨5576278910991143112149609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14870077095976381632398957 5576278910991143112149609)
    ·
      refine ⟨4182209183243357334112207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5576278910991143112149609 4182209183243357334112207)
      ·
        refine ⟨6273313774865036001168311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182209183243357334112207 6273313774865036001168311)
        ·
          refine ⟨9409970662297554001752467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6273313774865036001168311 9409970662297554001752467)
          ·
            refine ⟨14114955993446331002628701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9409970662297554001752467 14114955993446331002628701)
            ·
              refine ⟨5293108497542374125985763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14114955993446331002628701 5293108497542374125985763)
              ·
                refine ⟨7939662746313561188978645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5293108497542374125985763 7939662746313561188978645)
                ·
                  refine ⟨186085845616724090366687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7939662746313561188978645 186085845616724090366687)
                  ·
                    rfl

theorem cell20_407701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_407701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407701 prefixEnd_407701 := by exact prefixLift 407701
  have htrace : WordTrace (prefixWord ++ tailWord_407701) baseStart_407701 baseEnd_407701 := by
    simpa [prefixWord, tailWord_407701, baseEnd_407701] using wordTrace_append hprefix tailTrace_407701
  have hstable : (prefixWord ++ tailWord_407701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407701).length < 2 ^ (prefixWord ++ tailWord_407701).sum := by decide
  have hdescent : baseEnd_407701 < baseStart_407701 := by decide
  rcases family_descends (prefixWord ++ tailWord_407701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407711 : List Nat := [1, 1, 2, 6, 1, 3, 6]
def baseStart_407711 : Nat := 118140960795 + 407711 * 2 ^ 59
def prefixEnd_407711 : Nat := 4983230072969 + 3 ^ 40 * 407711 * 2
def baseEnd_407711 : Nat := 20676712209912055559257

theorem tailTrace_407711 : CollatzResearch.WordTrace tailWord_407711 prefixEnd_407711 20676712209912055559257 := by
  unfold tailWord_407711
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870441825940153340262987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9913627883960102226841991 14870441825940153340262987)
  ·
    refine ⟨22305662738910230010394481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14870441825940153340262987 22305662738910230010394481)
    ·
      refine ⟨16729247054182672507795861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22305662738910230010394481 16729247054182672507795861)
      ·
        refine ⟨784183455664812773802931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16729247054182672507795861 784183455664812773802931)
        ·
          refine ⟨1176275183497219160704397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784183455664812773802931 1176275183497219160704397)
          ·
            refine ⟨441103193811457185264149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1176275183497219160704397 441103193811457185264149)
            ·
              refine ⟨20676712209912055559257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 441103193811457185264149 20676712209912055559257)
              ·
                rfl

theorem cell20_407711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_407711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407711 prefixEnd_407711 := by exact prefixLift 407711
  have htrace : WordTrace (prefixWord ++ tailWord_407711) baseStart_407711 baseEnd_407711 := by
    simpa [prefixWord, tailWord_407711, baseEnd_407711] using wordTrace_append hprefix tailTrace_407711
  have hstable : (prefixWord ++ tailWord_407711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407711).length < 2 ^ (prefixWord ++ tailWord_407711).sum := by decide
  have hdescent : baseEnd_407711 < baseStart_407711 := by decide
  rcases family_descends (prefixWord ++ tailWord_407711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407735 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 3]
def baseStart_407735 : Nat := 118140960795 + 407735 * 2 ^ 59
def prefixEnd_407735 : Nat := 4983230072969 + 3 ^ 40 * 407735 * 2
def baseEnd_407735 : Nat := 186101364143171083233215

theorem tailTrace_407735 : CollatzResearch.WordTrace tailWord_407735 prefixEnd_407735 186101364143171083233215 := by
  unfold tailWord_407735
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871317177853205439136659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9914211451902136959424439 14871317177853205439136659)
  ·
    refine ⟨22306975766779808158704989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14871317177853205439136659 22306975766779808158704989)
    ·
      refine ⟨8365115912542428059514371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22306975766779808158704989 8365115912542428059514371)
      ·
        refine ⟨12547673868813642089271557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8365115912542428059514371 12547673868813642089271557)
        ·
          refine ⟨2352688850402557891738417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12547673868813642089271557 2352688850402557891738417)
          ·
            refine ⟨1764516637801918418803813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352688850402557891738417 1764516637801918418803813)
            ·
              refine ⟨330846869587859703525715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1764516637801918418803813 330846869587859703525715)
              ·
                refine ⟨496270304381789555288573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330846869587859703525715 496270304381789555288573)
                ·
                  refine ⟨186101364143171083233215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496270304381789555288573 186101364143171083233215)
                  ·
                    rfl

theorem cell20_407735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_407735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407735 prefixEnd_407735 := by exact prefixLift 407735
  have htrace : WordTrace (prefixWord ++ tailWord_407735) baseStart_407735 baseEnd_407735 := by
    simpa [prefixWord, tailWord_407735, baseEnd_407735] using wordTrace_append hprefix tailTrace_407735
  have hstable : (prefixWord ++ tailWord_407735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407735).length < 2 ^ (prefixWord ++ tailWord_407735).sum := by decide
  have hdescent : baseEnd_407735 < baseStart_407735 := by decide
  rcases family_descends (prefixWord ++ tailWord_407735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407772 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 2]
def baseStart_407772 : Nat := 118140960795 + 407772 * 2 ^ 59
def prefixEnd_407772 : Nat := 4983230072969 + 3 ^ 40 * 407772 * 2
def baseEnd_407772 : Nat := 186118251951363398999731

theorem tailTrace_407772 : CollatzResearch.WordTrace tailWord_407772 prefixEnd_407772 186118251951363398999731 := by
  unfold tailWord_407772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7436333339359580379116785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9915111119146107172155713 7436333339359580379116785)
  ·
    refine ⟨5577250004519685284337589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7436333339359580379116785 5577250004519685284337589)
    ·
      refine ⟨522867187923720495406649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5577250004519685284337589 522867187923720495406649)
      ·
        refine ⟨392150390942790371554987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522867187923720495406649 392150390942790371554987)
        ·
          refine ⟨588225586414185557332481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392150390942790371554987 588225586414185557332481)
          ·
            refine ⟨441169189810639167999361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588225586414185557332481 441169189810639167999361)
            ·
              refine ⟨330876892357979375999521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441169189810639167999361 330876892357979375999521)
              ·
                refine ⟨248157669268484531999641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330876892357979375999521 248157669268484531999641)
                ·
                  refine ⟨186118251951363398999731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248157669268484531999641 186118251951363398999731)
                  ·
                    rfl

theorem cell20_407772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_407772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407772 prefixEnd_407772 := by exact prefixLift 407772
  have htrace : WordTrace (prefixWord ++ tailWord_407772) baseStart_407772 baseEnd_407772 := by
    simpa [prefixWord, tailWord_407772, baseEnd_407772] using wordTrace_append hprefix tailTrace_407772
  have hstable : (prefixWord ++ tailWord_407772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407772).length < 2 ^ (prefixWord ++ tailWord_407772).sum := by decide
  have hdescent : baseEnd_407772 < baseStart_407772 := by decide
  rcases family_descends (prefixWord ++ tailWord_407772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407773 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_407773 : Nat := 118140960795 + 407773 * 2 ^ 59
def prefixEnd_407773 : Nat := 4983230072969 + 3 ^ 40 * 407773 * 2
def baseEnd_407773 : Nat := 186118708378611839966393

theorem tailTrace_407773 : CollatzResearch.WordTrace tailWord_407773 prefixEnd_407773 186118708378611839966393 := by
  unfold tailWord_407773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14872703151715537929019973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9915135434477025286013315 14872703151715537929019973)
  ·
    refine ⟨2788631840946663361691245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14872703151715537929019973 2788631840946663361691245)
    ·
      refine ⟨1045736940354998760634217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2788631840946663361691245 1045736940354998760634217)
      ·
        refine ⟨784302705266249070475663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1045736940354998760634217 784302705266249070475663)
        ·
          refine ⟨1176454057899373605713495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784302705266249070475663 1176454057899373605713495)
          ·
            refine ⟨1764681086849060408570243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176454057899373605713495 1764681086849060408570243)
            ·
              refine ⟨2647021630273590612855365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764681086849060408570243 2647021630273590612855365)
              ·
                refine ⟨496316555676298239910381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2647021630273590612855365 496316555676298239910381)
                ·
                  refine ⟨186118708378611839966393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496316555676298239910381 186118708378611839966393)
                  ·
                    rfl

theorem cell20_407773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_407773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407773 prefixEnd_407773 := by exact prefixLift 407773
  have htrace : WordTrace (prefixWord ++ tailWord_407773) baseStart_407773 baseEnd_407773 := by
    simpa [prefixWord, tailWord_407773, baseEnd_407773] using wordTrace_append hprefix tailTrace_407773
  have hstable : (prefixWord ++ tailWord_407773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407773).length < 2 ^ (prefixWord ++ tailWord_407773).sum := by decide
  have hdescent : baseEnd_407773 < baseStart_407773 := by decide
  rcases family_descends (prefixWord ++ tailWord_407773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407818 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_407818 : Nat := 118140960795 + 407818 * 2 ^ 59
def prefixEnd_407818 : Nat := 4983230072969 + 3 ^ 40 * 407818 * 2
def baseEnd_407818 : Nat := 186139247604791683466209

theorem tailTrace_407818 : CollatzResearch.WordTrace tailWord_407818 prefixEnd_407818 186139247604791683466209 := by
  unfold tailWord_407818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718586109138127653602027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9916229624368340409605405 3718586109138127653602027)
  ·
    refine ⟨5577879163707191480403041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3718586109138127653602027 5577879163707191480403041)
    ·
      refine ⟨4183409372780393610302281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5577879163707191480403041 4183409372780393610302281)
      ·
        refine ⟨3137557029585295207726711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4183409372780393610302281 3137557029585295207726711)
        ·
          refine ⟨4706335544377942811590067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137557029585295207726711 4706335544377942811590067)
          ·
            refine ⟨7059503316566914217385101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706335544377942811590067 7059503316566914217385101)
            ·
              refine ⟨2647313743712592831519413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7059503316566914217385101 2647313743712592831519413)
              ·
                refine ⟨248185663473055577954945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2647313743712592831519413 248185663473055577954945)
                ·
                  refine ⟨186139247604791683466209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248185663473055577954945 186139247604791683466209)
                  ·
                    rfl

theorem cell20_407818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_407818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407818 prefixEnd_407818 := by exact prefixLift 407818
  have htrace : WordTrace (prefixWord ++ tailWord_407818) baseStart_407818 baseEnd_407818 := by
    simpa [prefixWord, tailWord_407818, baseEnd_407818] using wordTrace_append hprefix tailTrace_407818
  have hstable : (prefixWord ++ tailWord_407818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407818).length < 2 ^ (prefixWord ++ tailWord_407818).sum := by decide
  have hdescent : baseEnd_407818 < baseStart_407818 := by decide
  rcases family_descends (prefixWord ++ tailWord_407818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407839 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_407839 : Nat := 118140960795 + 407839 * 2 ^ 59
def prefixEnd_407839 : Nat := 4983230072969 + 3 ^ 40 * 407839 * 2
def baseEnd_407839 : Nat := 186148832577008943766123

theorem tailTrace_407839 : CollatzResearch.WordTrace tailWord_407839 prefixEnd_407839 186148832577008943766123 := by
  unfold tailWord_407839
  simp only [CollatzResearch.WordTrace]
  refine ⟨14875110369476431200922571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9916740246317620800615047 14875110369476431200922571)
  ·
    refine ⟨22312665554214646801383857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14875110369476431200922571 22312665554214646801383857)
    ·
      refine ⟨16734499165660985101037893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22312665554214646801383857 16734499165660985101037893)
      ·
        refine ⟨3137718593561434706444605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16734499165660985101037893 3137718593561434706444605)
        ·
          refine ⟨1176644472585538014916727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3137718593561434706444605 1176644472585538014916727)
          ·
            refine ⟨1764966708878307022375091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176644472585538014916727 1764966708878307022375091)
            ·
              refine ⟨2647450063317460533562637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764966708878307022375091 2647450063317460533562637)
              ·
                refine ⟨992793773744047700085989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2647450063317460533562637 992793773744047700085989)
                ·
                  refine ⟨186148832577008943766123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 992793773744047700085989 186148832577008943766123)
                  ·
                    rfl

theorem cell20_407839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_407839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407839 prefixEnd_407839 := by exact prefixLift 407839
  have htrace : WordTrace (prefixWord ++ tailWord_407839) baseStart_407839 baseEnd_407839 := by
    simpa [prefixWord, tailWord_407839, baseEnd_407839] using wordTrace_append hprefix tailTrace_407839
  have hstable : (prefixWord ++ tailWord_407839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407839).length < 2 ^ (prefixWord ++ tailWord_407839).sum := by decide
  have hdescent : baseEnd_407839 < baseStart_407839 := by decide
  rcases family_descends (prefixWord ++ tailWord_407839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407870 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_407870 : Nat := 118140960795 + 407870 * 2 ^ 59
def prefixEnd_407870 : Nat := 4983230072969 + 3 ^ 40 * 407870 * 2
def baseEnd_407870 : Nat := 186162981821710613732663

theorem tailTrace_407870 : CollatzResearch.WordTrace tailWord_407870 prefixEnd_407870 186162981821710613732663 := by
  unfold tailWord_407870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859530129045515436912633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9917494021576082330200709 1859530129045515436912633)
  ·
    refine ⟨1394647596784136577684475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1859530129045515436912633 1394647596784136577684475)
    ·
      refine ⟨2091971395176204866526713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1394647596784136577684475 2091971395176204866526713)
      ·
        refine ⟨1568978546382153649895035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2091971395176204866526713 1568978546382153649895035)
        ·
          refine ⟨2353467819573230474842553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568978546382153649895035 2353467819573230474842553)
          ·
            refine ⟨1765100864679922856131915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353467819573230474842553 1765100864679922856131915)
            ·
              refine ⟨2647651297019884284197873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765100864679922856131915 2647651297019884284197873)
              ·
                refine ⟨1985738472764913213148405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647651297019884284197873 1985738472764913213148405)
                ·
                  refine ⟨186162981821710613732663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1985738472764913213148405 186162981821710613732663)
                  ·
                    rfl

theorem cell20_407870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_407870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407870 prefixEnd_407870 := by exact prefixLift 407870
  have htrace : WordTrace (prefixWord ++ tailWord_407870) baseStart_407870 baseEnd_407870 := by
    simpa [prefixWord, tailWord_407870, baseEnd_407870] using wordTrace_append hprefix tailTrace_407870
  have hstable : (prefixWord ++ tailWord_407870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407870).length < 2 ^ (prefixWord ++ tailWord_407870).sum := by decide
  have hdescent : baseEnd_407870 < baseStart_407870 := by decide
  rcases family_descends (prefixWord ++ tailWord_407870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407900 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 3]
def baseStart_407900 : Nat := 118140960795 + 407900 * 2 ^ 59
def prefixEnd_407900 : Nat := 4983230072969 + 3 ^ 40 * 407900 * 2
def baseEnd_407900 : Nat := 186176674639163842732541

theorem tailTrace_407900 : CollatzResearch.WordTrace tailWord_407900 prefixEnd_407900 186176674639163842732541 := by
  unfold tailWord_407900
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438667611127719309446577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9918223481503625745928769 7438667611127719309446577)
  ·
    refine ⟨5579000708345789482084933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7438667611127719309446577 5579000708345789482084933)
    ·
      refine ⟨1046062632814835527890925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5579000708345789482084933 1046062632814835527890925)
      ·
        refine ⟨392273487305563322959097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1046062632814835527890925 392273487305563322959097)
        ·
          refine ⟨294205115479172492219323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392273487305563322959097 294205115479172492219323)
          ·
            refine ⟨441307673218758738328985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294205115479172492219323 441307673218758738328985)
            ·
              refine ⟨330980754914069053746739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441307673218758738328985 330980754914069053746739)
              ·
                refine ⟨496471132371103580620109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330980754914069053746739 496471132371103580620109)
                ·
                  refine ⟨186176674639163842732541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496471132371103580620109 186176674639163842732541)
                  ·
                    rfl

theorem cell20_407900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_407900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407900 prefixEnd_407900 := by exact prefixLift 407900
  have htrace : WordTrace (prefixWord ++ tailWord_407900) baseStart_407900 baseEnd_407900 := by
    simpa [prefixWord, tailWord_407900, baseEnd_407900] using wordTrace_append hprefix tailTrace_407900
  have hstable : (prefixWord ++ tailWord_407900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407900).length < 2 ^ (prefixWord ++ tailWord_407900).sum := by decide
  have hdescent : baseEnd_407900 < baseStart_407900 := by decide
  rcases family_descends (prefixWord ++ tailWord_407900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407904 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_407904 : Nat := 118140960795 + 407904 * 2 ^ 59
def prefixEnd_407904 : Nat := 4983230072969 + 3 ^ 40 * 407904 * 2
def baseEnd_407904 : Nat := 186178500348157606599191

theorem tailTrace_407904 : CollatzResearch.WordTrace tailWord_407904 prefixEnd_407904 186178500348157606599191 := by
  unfold tailWord_407904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438740557120473651019383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9918320742827298201359177 7438740557120473651019383)
  ·
    refine ⟨11158110835680710476529075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7438740557120473651019383 11158110835680710476529075)
    ·
      refine ⟨16737166253521065714793613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11158110835680710476529075 16737166253521065714793613)
      ·
        refine ⟨6276437345070399643047605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16737166253521065714793613 6276437345070399643047605)
        ·
          refine ⟨588416001100349966535713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6276437345070399643047605 588416001100349966535713)
          ·
            refine ⟨441312000825262474901785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588416001100349966535713 441312000825262474901785)
            ·
              refine ⟨330984000618946856176339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441312000825262474901785 330984000618946856176339)
              ·
                refine ⟨496476000928420284264509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330984000618946856176339 496476000928420284264509)
                ·
                  refine ⟨186178500348157606599191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496476000928420284264509 186178500348157606599191)
                  ·
                    rfl

theorem cell20_407904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_407904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407904 prefixEnd_407904 := by exact prefixLift 407904
  have htrace : WordTrace (prefixWord ++ tailWord_407904) baseStart_407904 baseEnd_407904 := by
    simpa [prefixWord, tailWord_407904, baseEnd_407904] using wordTrace_append hprefix tailTrace_407904
  have hstable : (prefixWord ++ tailWord_407904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407904).length < 2 ^ (prefixWord ++ tailWord_407904).sum := by decide
  have hdescent : baseEnd_407904 < baseStart_407904 := by decide
  rcases family_descends (prefixWord ++ tailWord_407904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407908 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_407908 : Nat := 118140960795 + 407908 * 2 ^ 59
def prefixEnd_407908 : Nat := 4983230072969 + 3 ^ 40 * 407908 * 2
def baseEnd_407908 : Nat := 186180326057151370465841

theorem tailTrace_407908 : CollatzResearch.WordTrace tailWord_407908 prefixEnd_407908 186180326057151370465841 := by
  unfold tailWord_407908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438813503113227992592189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9918418004150970656789585 7438813503113227992592189)
  ·
    refine ⟨2789555063667460497222071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7438813503113227992592189 2789555063667460497222071)
    ·
      refine ⟨4184332595501190745833107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789555063667460497222071 4184332595501190745833107)
      ·
        refine ⟨6276498893251786118749661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4184332595501190745833107 6276498893251786118749661)
        ·
          refine ⟨2353687084969419794531123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6276498893251786118749661 2353687084969419794531123)
          ·
            refine ⟨3530530627454129691796685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353687084969419794531123 3530530627454129691796685)
            ·
              refine ⟨1323948985295298634423757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3530530627454129691796685 1323948985295298634423757)
              ·
                refine ⟨496480869485736987908909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323948985295298634423757 496480869485736987908909)
                ·
                  refine ⟨186180326057151370465841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496480869485736987908909 186180326057151370465841)
                  ·
                    rfl

theorem cell20_407908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_407908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407908 prefixEnd_407908 := by exact prefixLift 407908
  have htrace : WordTrace (prefixWord ++ tailWord_407908) baseStart_407908 baseEnd_407908 := by
    simpa [prefixWord, tailWord_407908, baseEnd_407908] using wordTrace_append hprefix tailTrace_407908
  have hstable : (prefixWord ++ tailWord_407908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407908).length < 2 ^ (prefixWord ++ tailWord_407908).sum := by decide
  have hdescent : baseEnd_407908 < baseStart_407908 := by decide
  rcases family_descends (prefixWord ++ tailWord_407908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407922 : List Nat := [3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_407922 : Nat := 118140960795 + 407922 * 2 ^ 59
def prefixEnd_407922 : Nat := 4983230072969 + 3 ^ 40 * 407922 * 2
def baseEnd_407922 : Nat := 62062238679543181333039

theorem tailTrace_407922 : CollatzResearch.WordTrace tailWord_407922 prefixEnd_407922 62062238679543181333039 := by
  unfold tailWord_407922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719534407043934094048505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9918758418783824250796013 3719534407043934094048505)
  ·
    refine ⟨2789650805282950570536379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3719534407043934094048505 2789650805282950570536379)
    ·
      refine ⟨4184476207924425855804569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789650805282950570536379 4184476207924425855804569)
      ·
        refine ⟨3138357155943319391853427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4184476207924425855804569 3138357155943319391853427)
        ·
          refine ⟨4707535733914979087780141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3138357155943319391853427 4707535733914979087780141)
          ·
            refine ⟨1765325900218117157917553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4707535733914979087780141 1765325900218117157917553)
            ·
              refine ⟨1323994425163587868438165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765325900218117157917553 1323994425163587868438165)
              ·
                refine ⟨62062238679543181333039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1323994425163587868438165 62062238679543181333039)
                ·
                  rfl

theorem cell20_407922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_407922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407922 prefixEnd_407922 := by exact prefixLift 407922
  have htrace : WordTrace (prefixWord ++ tailWord_407922) baseStart_407922 baseEnd_407922 := by
    simpa [prefixWord, tailWord_407922, baseEnd_407922] using wordTrace_append hprefix tailTrace_407922
  have hstable : (prefixWord ++ tailWord_407922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407922).length < 2 ^ (prefixWord ++ tailWord_407922).sum := by decide
  have hdescent : baseEnd_407922 < baseStart_407922 := by decide
  rcases family_descends (prefixWord ++ tailWord_407922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407956 : List Nat := [2, 4, 2, 1, 3, 2, 1, 5]
def baseStart_407956 : Nat := 118140960795 + 407956 * 2 ^ 59
def prefixEnd_407956 : Nat := 4983230072969 + 3 ^ 40 * 407956 * 2
def baseEnd_407956 : Nat := 62067411521692178955215

theorem tailTrace_407956 : CollatzResearch.WordTrace tailWord_407956 prefixEnd_407956 62067411521692178955215 := by
  unfold tailWord_407956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7439688855026280091465861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9919585140035040121954481 7439688855026280091465861)
  ·
    refine ⟨1394941660317427517149849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7439688855026280091465861 1394941660317427517149849)
    ·
      refine ⟨1046206245238070637862387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1394941660317427517149849 1046206245238070637862387)
      ·
        refine ⟨1569309367857105956793581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046206245238070637862387 1569309367857105956793581)
        ·
          refine ⟨588491012946414733797593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1569309367857105956793581 588491012946414733797593)
          ·
            refine ⟨441368259709811050348195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588491012946414733797593 441368259709811050348195)
            ·
              refine ⟨662052389564716575522293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441368259709811050348195 662052389564716575522293)
              ·
                refine ⟨62067411521692178955215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662052389564716575522293 62067411521692178955215)
                ·
                  rfl

theorem cell20_407956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_407956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_407956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_407956 prefixEnd_407956 := by exact prefixLift 407956
  have htrace : WordTrace (prefixWord ++ tailWord_407956) baseStart_407956 baseEnd_407956 := by
    simpa [prefixWord, tailWord_407956, baseEnd_407956] using wordTrace_append hprefix tailTrace_407956
  have hstable : (prefixWord ++ tailWord_407956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407956).length < 2 ^ (prefixWord ++ tailWord_407956).sum := by decide
  have hdescent : baseEnd_407956 < baseStart_407956 := by decide
  rcases family_descends (prefixWord ++ tailWord_407956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408008 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 2]
def baseStart_408008 : Nat := 118140960795 + 408008 * 2 ^ 59
def prefixEnd_408008 : Nat := 4983230072969 + 3 ^ 40 * 408008 * 2
def baseEnd_408008 : Nat := 186225968781995467132099

theorem tailTrace_408008 : CollatzResearch.WordTrace tailWord_408008 prefixEnd_408008 186225968781995467132099 := by
  unfold tailWord_408008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440637152932086531912339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9920849537242782042549785 7440637152932086531912339)
  ·
    refine ⟨11160955729398129797868509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7440637152932086531912339 11160955729398129797868509)
    ·
      refine ⟨4185358398524298674200691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11160955729398129797868509 4185358398524298674200691)
      ·
        refine ⟨6278037597786448011301037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185358398524298674200691 6278037597786448011301037)
        ·
          refine ⟨2354264099169918004237889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6278037597786448011301037 2354264099169918004237889)
          ·
            refine ⟨1765698074377438503178417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354264099169918004237889 1765698074377438503178417)
            ·
              refine ⟨1324273555783078877383813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1765698074377438503178417 1324273555783078877383813)
              ·
                refine ⟨248301291709327289509465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1324273555783078877383813 248301291709327289509465)
                ·
                  refine ⟨186225968781995467132099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248301291709327289509465 186225968781995467132099)
                  ·
                    rfl

theorem cell20_408008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_408008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408008 prefixEnd_408008 := by exact prefixLift 408008
  have htrace : WordTrace (prefixWord ++ tailWord_408008) baseStart_408008 baseEnd_408008 := by
    simpa [prefixWord, tailWord_408008, baseEnd_408008] using wordTrace_append hprefix tailTrace_408008
  have hstable : (prefixWord ++ tailWord_408008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408008).length < 2 ^ (prefixWord ++ tailWord_408008).sum := by decide
  have hdescent : baseEnd_408008 < baseStart_408008 := by decide
  rcases family_descends (prefixWord ++ tailWord_408008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408029 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_408029 : Nat := 118140960795 + 408029 * 2 ^ 59
def prefixEnd_408029 : Nat := 4983230072969 + 3 ^ 40 * 408029 * 2
def baseEnd_408029 : Nat := 186235553754212727432013

theorem tailTrace_408029 : CollatzResearch.WordTrace tailWord_408029 prefixEnd_408029 186235553754212727432013 := by
  unfold tailWord_408029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14882040238788093650339141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9921360159192062433559427 14882040238788093650339141)
  ·
    refine ⟨2790382544772767559438589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14882040238788093650339141 2790382544772767559438589)
    ·
      refine ⟨1046393454289787834789471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2790382544772767559438589 1046393454289787834789471)
      ·
        refine ⟨1569590181434681752184207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046393454289787834789471 1569590181434681752184207)
        ·
          refine ⟨2354385272152022628276311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569590181434681752184207 2354385272152022628276311)
          ·
            refine ⟨3531577908228033942414467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354385272152022628276311 3531577908228033942414467)
            ·
              refine ⟨5297366862342050913621701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3531577908228033942414467 5297366862342050913621701)
              ·
                refine ⟨993256286689134546304069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5297366862342050913621701 993256286689134546304069)
                ·
                  refine ⟨186235553754212727432013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 993256286689134546304069 186235553754212727432013)
                  ·
                    rfl

theorem cell20_408029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_408029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408029 prefixEnd_408029 := by exact prefixLift 408029
  have htrace : WordTrace (prefixWord ++ tailWord_408029) baseStart_408029 baseEnd_408029 := by
    simpa [prefixWord, tailWord_408029, baseEnd_408029] using wordTrace_append hprefix tailTrace_408029
  have hstable : (prefixWord ++ tailWord_408029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408029).length < 2 ^ (prefixWord ++ tailWord_408029).sum := by decide
  have hdescent : baseEnd_408029 < baseStart_408029 := by decide
  rcases family_descends (prefixWord ++ tailWord_408029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408057 : List Nat := [1, 2, 1, 3, 1, 2, 10]
def baseStart_408057 : Nat := 118140960795 + 408057 * 2 ^ 59
def prefixEnd_408057 : Nat := 4983230072969 + 3 ^ 40 * 408057 * 2
def baseEnd_408057 : Nat := 20694259301907674944285

theorem tailTrace_408057 : CollatzResearch.WordTrace tailWord_408057 prefixEnd_408057 20694259301907674944285 := by
  unfold tailWord_408057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883061482686654432358425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9922040988457769621572283 14883061482686654432358425)
  ·
    refine ⟨11162296112014990824268819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14883061482686654432358425 11162296112014990824268819)
    ·
      refine ⟨16743444168022486236403229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11162296112014990824268819 16743444168022486236403229)
      ·
        refine ⟨6278791563008432338651211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16743444168022486236403229 6278791563008432338651211)
        ·
          refine ⟨9418187344512648507976817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278791563008432338651211 9418187344512648507976817)
          ·
            refine ⟨7063640508384486380982613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9418187344512648507976817 7063640508384486380982613)
            ·
              refine ⟨20694259301907674944285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7063640508384486380982613 20694259301907674944285)
              ·
                rfl

theorem cell20_408057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_408057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408057 prefixEnd_408057 := by exact prefixLift 408057
  have htrace : WordTrace (prefixWord ++ tailWord_408057) baseStart_408057 baseEnd_408057 := by
    simpa [prefixWord, tailWord_408057, baseEnd_408057] using wordTrace_append hprefix tailTrace_408057
  have hstable : (prefixWord ++ tailWord_408057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408057).length < 2 ^ (prefixWord ++ tailWord_408057).sum := by decide
  have hdescent : baseEnd_408057 < baseStart_408057 := by decide
  rcases family_descends (prefixWord ++ tailWord_408057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408074 : List Nat := [3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_408074 : Nat := 118140960795 + 408074 * 2 ^ 59
def prefixEnd_408074 : Nat := 4983230072969 + 3 ^ 40 * 408074 * 2
def baseEnd_408074 : Nat := 62085364326797523643943

theorem tailTrace_408074 : CollatzResearch.WordTrace tailWord_408074 prefixEnd_408074 62085364326797523643943 := by
  unfold tailWord_408074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720920380906266583931819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9922454349083377557151517 3720920380906266583931819)
  ·
    refine ⟨5581380571359399875897729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720920380906266583931819 5581380571359399875897729)
    ·
      refine ⟨4186035428519549906923297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5581380571359399875897729 4186035428519549906923297)
      ·
        refine ⟨3139526571389662430192473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4186035428519549906923297 3139526571389662430192473)
        ·
          refine ⟨2354644928542246822644355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139526571389662430192473 2354644928542246822644355)
          ·
            refine ⟨3531967392813370233966533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354644928542246822644355 3531967392813370233966533)
            ·
              refine ⟨662243886152506918868725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3531967392813370233966533 662243886152506918868725)
              ·
                refine ⟨62085364326797523643943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662243886152506918868725 62085364326797523643943)
                ·
                  rfl

theorem cell20_408074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_408074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408074 prefixEnd_408074 := by exact prefixLift 408074
  have htrace : WordTrace (prefixWord ++ tailWord_408074) baseStart_408074 baseEnd_408074 := by
    simpa [prefixWord, tailWord_408074, baseEnd_408074] using wordTrace_append hprefix tailTrace_408074
  have hstable : (prefixWord ++ tailWord_408074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408074).length < 2 ^ (prefixWord ++ tailWord_408074).sum := by decide
  have hdescent : baseEnd_408074 < baseStart_408074 := by decide
  rcases family_descends (prefixWord ++ tailWord_408074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408118 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_408118 : Nat := 118140960795 + 408118 * 2 ^ 59
def prefixEnd_408118 : Nat := 4983230072969 + 3 ^ 40 * 408118 * 2
def baseEnd_408118 : Nat := 186276175779323973464983

theorem tailTrace_408118 : CollatzResearch.WordTrace tailWord_408118 prefixEnd_408118 186276175779323973464983 := by
  unfold tailWord_408118
  simp only [CollatzResearch.WordTrace]
  refine ⟨930330395966603865645563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9923524223643774566886005 930330395966603865645563)
  ·
    refine ⟨1395495593949905798468345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 930330395966603865645563 1395495593949905798468345)
    ·
      refine ⟨1046621695462429348851259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1395495593949905798468345 1046621695462429348851259)
      ·
        refine ⟨1569932543193644023276889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046621695462429348851259 1569932543193644023276889)
        ·
          refine ⟨1177449407395233017457667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1569932543193644023276889 1177449407395233017457667)
          ·
            refine ⟨1766174111092849526186501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177449407395233017457667 1766174111092849526186501)
            ·
              refine ⟨331157645829909286159969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1766174111092849526186501 331157645829909286159969)
              ·
                refine ⟨248368234372431964619977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331157645829909286159969 248368234372431964619977)
                ·
                  refine ⟨186276175779323973464983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248368234372431964619977 186276175779323973464983)
                  ·
                    rfl

theorem cell20_408118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_408118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408118 prefixEnd_408118 := by exact prefixLift 408118
  have htrace : WordTrace (prefixWord ++ tailWord_408118) baseStart_408118 baseEnd_408118 := by
    simpa [prefixWord, tailWord_408118, baseEnd_408118] using wordTrace_append hprefix tailTrace_408118
  have hstable : (prefixWord ++ tailWord_408118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408118).length < 2 ^ (prefixWord ++ tailWord_408118).sum := by decide
  have hdescent : baseEnd_408118 < baseStart_408118 := by decide
  rcases family_descends (prefixWord ++ tailWord_408118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408122 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_408122 : Nat := 118140960795 + 408122 * 2 ^ 59
def prefixEnd_408122 : Nat := 4983230072969 + 3 ^ 40 * 408122 * 2
def baseEnd_408122 : Nat := 186278001488317737331633

theorem tailTrace_408122 : CollatzResearch.WordTrace tailWord_408122 prefixEnd_408122 186278001488317737331633 := by
  unfold tailWord_408122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721358056862792633368655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9923621484967447022316413 3721358056862792633368655)
  ·
    refine ⟨5582037085294188950052983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721358056862792633368655 5582037085294188950052983)
    ·
      refine ⟨8373055627941283425079475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582037085294188950052983 8373055627941283425079475)
      ·
        refine ⟨12559583441911925137619213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8373055627941283425079475 12559583441911925137619213)
        ·
          refine ⟨4709843790716971926607205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12559583441911925137619213 4709843790716971926607205)
          ·
            refine ⟨883095710759432236238851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4709843790716971926607205 883095710759432236238851)
            ·
              refine ⟨1324643566139148354358277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883095710759432236238851 1324643566139148354358277)
              ·
                refine ⟨248370668651090316442177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1324643566139148354358277 248370668651090316442177)
                ·
                  refine ⟨186278001488317737331633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248370668651090316442177 186278001488317737331633)
                  ·
                    rfl

theorem cell20_408122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_408122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408122 prefixEnd_408122 := by exact prefixLift 408122
  have htrace : WordTrace (prefixWord ++ tailWord_408122) baseStart_408122 baseEnd_408122 := by
    simpa [prefixWord, tailWord_408122, baseEnd_408122] using wordTrace_append hprefix tailTrace_408122
  have hstable : (prefixWord ++ tailWord_408122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408122).length < 2 ^ (prefixWord ++ tailWord_408122).sum := by decide
  have hdescent : baseEnd_408122 < baseStart_408122 := by decide
  rcases family_descends (prefixWord ++ tailWord_408122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408129 : List Nat := [1, 2, 5, 1, 1, 4, 1, 5]
def baseStart_408129 : Nat := 118140960795 + 408129 * 2 ^ 59
def prefixEnd_408129 : Nat := 4983230072969 + 3 ^ 40 * 408129 * 2
def baseEnd_408129 : Nat := 62093732159685608032757

theorem tailTrace_408129 : CollatzResearch.WordTrace tailWord_408129 prefixEnd_408129 62093732159685608032757 := by
  unfold tailWord_408129
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885687538425810728979441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9923791692283873819319627 14885687538425810728979441)
  ·
    refine ⟨11164265653819358046734581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14885687538425810728979441 11164265653819358046734581)
    ·
      refine ⟨1046649905045564816881367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11164265653819358046734581 1046649905045564816881367)
      ·
        refine ⟨1569974857568347225322051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046649905045564816881367 1569974857568347225322051)
        ·
          refine ⟨2354962286352520837983077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569974857568347225322051 2354962286352520837983077)
          ·
            refine ⟨441555428691097657121827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2354962286352520837983077 441555428691097657121827)
            ·
              refine ⟨662333143036646485682741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441555428691097657121827 662333143036646485682741)
              ·
                refine ⟨62093732159685608032757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662333143036646485682741 62093732159685608032757)
                ·
                  rfl

theorem cell20_408129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 5].length) (baseStart_408129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408129 prefixEnd_408129 := by exact prefixLift 408129
  have htrace : WordTrace (prefixWord ++ tailWord_408129) baseStart_408129 baseEnd_408129 := by
    simpa [prefixWord, tailWord_408129, baseEnd_408129] using wordTrace_append hprefix tailTrace_408129
  have hstable : (prefixWord ++ tailWord_408129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408129).length < 2 ^ (prefixWord ++ tailWord_408129).sum := by decide
  have hdescent : baseEnd_408129 < baseStart_408129 := by decide
  rcases family_descends (prefixWord ++ tailWord_408129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408164 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_408164 : Nat := 118140960795 + 408164 * 2 ^ 59
def prefixEnd_408164 : Nat := 4983230072969 + 3 ^ 40 * 408164 * 2
def baseEnd_408164 : Nat := 186297171432752257931461

theorem tailTrace_408164 : CollatzResearch.WordTrace tailWord_408164 prefixEnd_408164 186297171432752257931461 := by
  unfold tailWord_408164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443482046649505853251773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9924642728866007804335697 7443482046649505853251773)
  ·
    refine ⟨2791305767493564694969415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7443482046649505853251773 2791305767493564694969415)
    ·
      refine ⟨4186958651240347042454123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791305767493564694969415 4186958651240347042454123)
      ·
        refine ⟨6280437976860520563681185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186958651240347042454123 6280437976860520563681185)
        ·
          refine ⟨4710328482645390422760889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6280437976860520563681185 4710328482645390422760889)
          ·
            refine ⟨3532746361984042817070667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4710328482645390422760889 3532746361984042817070667)
            ·
              refine ⟨5299119542976064225606001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532746361984042817070667 5299119542976064225606001)
              ·
                refine ⟨3974339657232048169204501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299119542976064225606001 3974339657232048169204501)
                ·
                  refine ⟨186297171432752257931461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3974339657232048169204501 186297171432752257931461)
                  ·
                    rfl

theorem cell20_408164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_408164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408164 prefixEnd_408164 := by exact prefixLift 408164
  have htrace : WordTrace (prefixWord ++ tailWord_408164) baseStart_408164 baseEnd_408164 := by
    simpa [prefixWord, tailWord_408164, baseEnd_408164] using wordTrace_append hprefix tailTrace_408164
  have hstable : (prefixWord ++ tailWord_408164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408164).length < 2 ^ (prefixWord ++ tailWord_408164).sum := by decide
  have hdescent : baseEnd_408164 < baseStart_408164 := by decide
  rcases family_descends (prefixWord ++ tailWord_408164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408174 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_408174 : Nat := 118140960795 + 408174 * 2 ^ 59
def prefixEnd_408174 : Nat := 4983230072969 + 3 ^ 40 * 408174 * 2
def baseEnd_408174 : Nat := 186301735705236667598087

theorem tailTrace_408174 : CollatzResearch.WordTrace tailWord_408174 prefixEnd_408174 186301735705236667598087 := by
  unfold tailWord_408174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860916102907847926795947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9924885882175188942911717 1860916102907847926795947)
  ·
    refine ⟨2791374154361771890193921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860916102907847926795947 2791374154361771890193921)
    ·
      refine ⟨2093530615771328917645441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2791374154361771890193921 2093530615771328917645441)
      ·
        refine ⟨1570147961828496688234081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093530615771328917645441 1570147961828496688234081)
        ·
          refine ⟨1177610971371372516175561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570147961828496688234081 1177610971371372516175561)
          ·
            refine ⟨883208228528529387131671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177610971371372516175561 883208228528529387131671)
            ·
              refine ⟨1324812342792794080697507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883208228528529387131671 1324812342792794080697507)
              ·
                refine ⟨1987218514189191121046261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324812342792794080697507 1987218514189191121046261)
                ·
                  refine ⟨186301735705236667598087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987218514189191121046261 186301735705236667598087)
                  ·
                    rfl

theorem cell20_408174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_408174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408174 prefixEnd_408174 := by exact prefixLift 408174
  have htrace : WordTrace (prefixWord ++ tailWord_408174) baseStart_408174 baseEnd_408174 := by
    simpa [prefixWord, tailWord_408174, baseEnd_408174] using wordTrace_append hprefix tailTrace_408174
  have hstable : (prefixWord ++ tailWord_408174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408174).length < 2 ^ (prefixWord ++ tailWord_408174).sum := by decide
  have hdescent : baseEnd_408174 < baseStart_408174 := by decide
  rcases family_descends (prefixWord ++ tailWord_408174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408195 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_408195 : Nat := 118140960795 + 408195 * 2 ^ 59
def prefixEnd_408195 : Nat := 4983230072969 + 3 ^ 40 * 408195 * 2
def baseEnd_408195 : Nat := 186311320677453927898001

theorem tailTrace_408195 : CollatzResearch.WordTrace tailWord_408195 prefixEnd_408195 186311320677453927898001 := by
  unfold tailWord_408195
  simp only [CollatzResearch.WordTrace]
  refine ⟨14888094756186704000882039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9925396504124469333921359 14888094756186704000882039)
  ·
    refine ⟨22332142134280056001323059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14888094756186704000882039 22332142134280056001323059)
    ·
      refine ⟨33498213201420084001984589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22332142134280056001323059 33498213201420084001984589)
      ·
        refine ⟨12561829950532531500744221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33498213201420084001984589 12561829950532531500744221)
        ·
          refine ⟨4710686231449699312779083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12561829950532531500744221 4710686231449699312779083)
          ·
            refine ⟨7066029347174548969168625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710686231449699312779083 7066029347174548969168625)
            ·
              refine ⟨5299522010380911726876469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066029347174548969168625 5299522010380911726876469)
              ·
                refine ⟨496830188473210474394669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5299522010380911726876469 496830188473210474394669)
                ·
                  refine ⟨186311320677453927898001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496830188473210474394669 186311320677453927898001)
                  ·
                    rfl

theorem cell20_408195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_408195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408195 prefixEnd_408195 := by exact prefixLift 408195
  have htrace : WordTrace (prefixWord ++ tailWord_408195) baseStart_408195 baseEnd_408195 := by
    simpa [prefixWord, tailWord_408195, baseEnd_408195] using wordTrace_append hprefix tailTrace_408195
  have hstable : (prefixWord ++ tailWord_408195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408195).length < 2 ^ (prefixWord ++ tailWord_408195).sum := by decide
  have hdescent : baseEnd_408195 < baseStart_408195 := by decide
  rcases family_descends (prefixWord ++ tailWord_408195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408212 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_408212 : Nat := 118140960795 + 408212 * 2 ^ 59
def prefixEnd_408212 : Nat := 4983230072969 + 3 ^ 40 * 408212 * 2
def baseEnd_408212 : Nat := 186319079940677424331265

theorem tailTrace_408212 : CollatzResearch.WordTrace tailWord_408212 prefixEnd_408212 186319079940677424331265 := by
  unfold tailWord_408212
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444357398562557952125445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9925809864750077269500593 7444357398562557952125445)
  ·
    refine ⟨1395817012230479616023521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7444357398562557952125445 1395817012230479616023521)
    ·
      refine ⟨1046862759172859712017641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1395817012230479616023521 1046862759172859712017641)
      ·
        refine ⟨785147069379644784013231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1046862759172859712017641 785147069379644784013231)
        ·
          refine ⟨1177720604069467176019847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785147069379644784013231 1177720604069467176019847)
          ·
            refine ⟨1766580906104200764029771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177720604069467176019847 1766580906104200764029771)
            ·
              refine ⟨2649871359156301146044657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766580906104200764029771 2649871359156301146044657)
              ·
                refine ⟨1987403519367225859533493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649871359156301146044657 1987403519367225859533493)
                ·
                  refine ⟨186319079940677424331265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1987403519367225859533493 186319079940677424331265)
                  ·
                    rfl

theorem cell20_408212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_408212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408212 prefixEnd_408212 := by exact prefixLift 408212
  have htrace : WordTrace (prefixWord ++ tailWord_408212) baseStart_408212 baseEnd_408212 := by
    simpa [prefixWord, tailWord_408212, baseEnd_408212] using wordTrace_append hprefix tailTrace_408212
  have hstable : (prefixWord ++ tailWord_408212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408212).length < 2 ^ (prefixWord ++ tailWord_408212).sum := by decide
  have hdescent : baseEnd_408212 < baseStart_408212 := by decide
  rcases family_descends (prefixWord ++ tailWord_408212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408246 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_408246 : Nat := 118140960795 + 408246 * 2 ^ 59
def prefixEnd_408246 : Nat := 4983230072969 + 3 ^ 40 * 408246 * 2
def baseEnd_408246 : Nat := 186334598467124417197793

theorem tailTrace_408246 : CollatzResearch.WordTrace tailWord_408246 prefixEnd_408246 186334598467124417197793 := by
  unfold tailWord_408246
  simp only [CollatzResearch.WordTrace]
  refine ⟨930622179937621231936787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9926636586001293140659061 930622179937621231936787)
  ·
    refine ⟨1395933269906431847905181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 930622179937621231936787 1395933269906431847905181)
    ·
      refine ⟨523474976214911942964443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1395933269906431847905181 523474976214911942964443)
      ·
        refine ⟨785212464322367914446665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523474976214911942964443 785212464322367914446665)
        ·
          refine ⟨588909348241775935834999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785212464322367914446665 588909348241775935834999)
          ·
            refine ⟨883364022362663903752499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588909348241775935834999 883364022362663903752499)
            ·
              refine ⟨1325046033543995855628749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883364022362663903752499 1325046033543995855628749)
              ·
                refine ⟨496892262578998445860781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1325046033543995855628749 496892262578998445860781)
                ·
                  refine ⟨186334598467124417197793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 496892262578998445860781 186334598467124417197793)
                  ·
                    rfl

theorem cell20_408246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_408246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408246 prefixEnd_408246 := by exact prefixLift 408246
  have htrace : WordTrace (prefixWord ++ tailWord_408246) baseStart_408246 baseEnd_408246 := by
    simpa [prefixWord, tailWord_408246, baseEnd_408246] using wordTrace_append hprefix tailTrace_408246
  have hstable : (prefixWord ++ tailWord_408246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408246).length < 2 ^ (prefixWord ++ tailWord_408246).sum := by decide
  have hdescent : baseEnd_408246 < baseStart_408246 := by decide
  rcases family_descends (prefixWord ++ tailWord_408246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408285 : List Nat := [1, 4, 3, 12]
def baseStart_408285 : Nat := 118140960795 + 408285 * 2 ^ 59
def prefixEnd_408285 : Nat := 4983230072969 + 3 ^ 40 * 408285 * 2
def baseEnd_408285 : Nat := 766882300945735040731

theorem tailTrace_408285 : CollatzResearch.WordTrace tailWord_408285 prefixEnd_408285 766882300945735040731 := by
  unfold tailWord_408285
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891377325860649371658309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9927584883907099581105539 14891377325860649371658309)
  ·
    refine ⟨2792133248598871757185933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14891377325860649371658309 2792133248598871757185933)
    ·
      refine ⟨1047049968224576908944725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2792133248598871757185933 1047049968224576908944725)
      ·
        refine ⟨766882300945735040731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1047049968224576908944725 766882300945735040731)
        ·
          rfl

theorem cell20_408285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 12].length) (baseStart_408285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408285 prefixEnd_408285 := by exact prefixLift 408285
  have htrace : WordTrace (prefixWord ++ tailWord_408285) baseStart_408285 baseEnd_408285 := by
    simpa [prefixWord, tailWord_408285, baseEnd_408285] using wordTrace_append hprefix tailTrace_408285
  have hstable : (prefixWord ++ tailWord_408285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408285).length < 2 ^ (prefixWord ++ tailWord_408285).sum := by decide
  have hdescent : baseEnd_408285 < baseStart_408285 := by decide
  rcases family_descends (prefixWord ++ tailWord_408285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408291 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 2]
def baseStart_408291 : Nat := 118140960795 + 408291 * 2 ^ 59
def prefixEnd_408291 : Nat := 4983230072969 + 3 ^ 40 * 408291 * 2
def baseEnd_408291 : Nat := 186355137693304260697609

theorem tailTrace_408291 : CollatzResearch.WordTrace tailWord_408291 prefixEnd_408291 186355137693304260697609 := by
  unfold tailWord_408291
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891596163838912396376727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9927730775892608264251151 14891596163838912396376727)
  ·
    refine ⟨22337394245758368594565091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14891596163838912396376727 22337394245758368594565091)
    ·
      refine ⟨33506091368637552891847637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22337394245758368594565091 33506091368637552891847637)
      ·
        refine ⟨785299016452442645902679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33506091368637552891847637 785299016452442645902679)
        ·
          refine ⟨1177948524678663968854019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785299016452442645902679 1177948524678663968854019)
          ·
            refine ⟨1766922787017995953281029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177948524678663968854019 1766922787017995953281029)
            ·
              refine ⟨331298022565874241240193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1766922787017995953281029 331298022565874241240193)
              ·
                refine ⟨248473516924405680930145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331298022565874241240193 248473516924405680930145)
                ·
                  refine ⟨186355137693304260697609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248473516924405680930145 186355137693304260697609)
                  ·
                    rfl

theorem cell20_408291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 2].length) (baseStart_408291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408291 prefixEnd_408291 := by exact prefixLift 408291
  have htrace : WordTrace (prefixWord ++ tailWord_408291) baseStart_408291 baseEnd_408291 := by
    simpa [prefixWord, tailWord_408291, baseEnd_408291] using wordTrace_append hprefix tailTrace_408291
  have hstable : (prefixWord ++ tailWord_408291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408291).length < 2 ^ (prefixWord ++ tailWord_408291).sum := by decide
  have hdescent : baseEnd_408291 < baseStart_408291 := by decide
  rcases family_descends (prefixWord ++ tailWord_408291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408302 : List Nat := [4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_408302 : Nat := 118140960795 + 408302 * 2 ^ 59
def prefixEnd_408302 : Nat := 4983230072969 + 3 ^ 40 * 408302 * 2
def baseEnd_408302 : Nat := 62120052797679037110299

theorem tailTrace_408302 : CollatzResearch.WordTrace tailWord_408302 prefixEnd_408302 62120052797679037110299 := by
  unfold tailWord_408302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861499670849882659378395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9927998244532707516684773 1861499670849882659378395)
  ·
    refine ⟨2792249506274823989067593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1861499670849882659378395 2792249506274823989067593)
    ·
      refine ⟨2094187129706117991800695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2792249506274823989067593 2094187129706117991800695)
      ·
        refine ⟨3141280694559176987701043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094187129706117991800695 3141280694559176987701043)
        ·
          refine ⟨4711921041838765481551565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141280694559176987701043 4711921041838765481551565)
          ·
            refine ⟨1766970390689537055581837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4711921041838765481551565 1766970390689537055581837)
            ·
              refine ⟨662613896508576395843189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766970390689537055581837 662613896508576395843189)
              ·
                refine ⟨62120052797679037110299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 662613896508576395843189 62120052797679037110299)
                ·
                  rfl

theorem cell20_408302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_408302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408302 prefixEnd_408302 := by exact prefixLift 408302
  have htrace : WordTrace (prefixWord ++ tailWord_408302) baseStart_408302 baseEnd_408302 := by
    simpa [prefixWord, tailWord_408302, baseEnd_408302] using wordTrace_append hprefix tailTrace_408302
  have hstable : (prefixWord ++ tailWord_408302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408302).length < 2 ^ (prefixWord ++ tailWord_408302).sum := by decide
  have hdescent : baseEnd_408302 < baseStart_408302 := by decide
  rcases family_descends (prefixWord ++ tailWord_408302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408316 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_408316 : Nat := 118140960795 + 408316 * 2 ^ 59
def prefixEnd_408316 : Nat := 4983230072969 + 3 ^ 40 * 408316 * 2
def baseEnd_408316 : Nat := 186366548374515284864173

theorem tailTrace_408316 : CollatzResearch.WordTrace tailWord_408316 prefixEnd_408316 186366548374515284864173 := by
  unfold tailWord_408316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446253994374170833018401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9928338659165561110691201 7446253994374170833018401)
  ·
    refine ⟨5584690495780628124763801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7446253994374170833018401 5584690495780628124763801)
    ·
      refine ⟨4188517871835471093572851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5584690495780628124763801 4188517871835471093572851)
      ·
        refine ⟨6282776807753206640359277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4188517871835471093572851 6282776807753206640359277)
        ·
          refine ⟨2356041302907452490134729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6282776807753206640359277 2356041302907452490134729)
          ·
            refine ⟨1767030977180589367601047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2356041302907452490134729 1767030977180589367601047)
            ·
              refine ⟨2650546465770884051401571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767030977180589367601047 2650546465770884051401571)
              ·
                refine ⟨3975819698656326077102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650546465770884051401571 3975819698656326077102357)
                ·
                  refine ⟨186366548374515284864173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3975819698656326077102357 186366548374515284864173)
                  ·
                    rfl

theorem cell20_408316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_408316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408316 prefixEnd_408316 := by exact prefixLift 408316
  have htrace : WordTrace (prefixWord ++ tailWord_408316) baseStart_408316 baseEnd_408316 := by
    simpa [prefixWord, tailWord_408316, baseEnd_408316] using wordTrace_append hprefix tailTrace_408316
  have hstable : (prefixWord ++ tailWord_408316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408316).length < 2 ^ (prefixWord ++ tailWord_408316).sum := by decide
  have hdescent : baseEnd_408316 < baseStart_408316 := by decide
  rcases family_descends (prefixWord ++ tailWord_408316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408343 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 3]
def baseStart_408343 : Nat := 118140960795 + 408343 * 2 ^ 59
def prefixEnd_408343 : Nat := 4983230072969 + 3 ^ 40 * 408343 * 2
def baseEnd_408343 : Nat := 186378871910223190964063

theorem tailTrace_408343 : CollatzResearch.WordTrace tailWord_408343 prefixEnd_408343 186378871910223190964063 := by
  unfold tailWord_408343
  simp only [CollatzResearch.WordTrace]
  refine ⟨14893492759650525277269683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9928995173100350184846455 14893492759650525277269683)
  ·
    refine ⟨22340239139475787915904525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14893492759650525277269683 22340239139475787915904525)
    ·
      refine ⟨8377589677303420468464197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22340239139475787915904525 8377589677303420468464197)
      ·
        refine ⟨1570798064494391337837037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8377589677303420468464197 1570798064494391337837037)
        ·
          refine ⟨589049274185396751688889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1570798064494391337837037 589049274185396751688889)
          ·
            refine ⟨441786955639047563766667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589049274185396751688889 441786955639047563766667)
            ·
              refine ⟨662680433458571345650001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441786955639047563766667 662680433458571345650001)
              ·
                refine ⟨497010325093928509237501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662680433458571345650001 497010325093928509237501)
                ·
                  refine ⟨186378871910223190964063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497010325093928509237501 186378871910223190964063)
                  ·
                    rfl

theorem cell20_408343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_408343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408343 prefixEnd_408343 := by exact prefixLift 408343
  have htrace : WordTrace (prefixWord ++ tailWord_408343) baseStart_408343 baseEnd_408343 := by
    simpa [prefixWord, tailWord_408343, baseEnd_408343] using wordTrace_append hprefix tailTrace_408343
  have hstable : (prefixWord ++ tailWord_408343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408343).length < 2 ^ (prefixWord ++ tailWord_408343).sum := by decide
  have hdescent : baseEnd_408343 < baseStart_408343 := by decide
  rcases family_descends (prefixWord ++ tailWord_408343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408364 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_408364 : Nat := 118140960795 + 408364 * 2 ^ 59
def prefixEnd_408364 : Nat := 4983230072969 + 3 ^ 40 * 408364 * 2
def baseEnd_408364 : Nat := 186388456882440451263977

theorem tailTrace_408364 : CollatzResearch.WordTrace tailWord_408364 prefixEnd_408364 186388456882440451263977 := by
  unfold tailWord_408364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447129346287222931892073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9929505795049630575856097 7447129346287222931892073)
  ·
    refine ⟨5585347009715417198919055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7447129346287222931892073 5585347009715417198919055)
    ·
      refine ⟨8378020514573125798378583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585347009715417198919055 8378020514573125798378583)
      ·
        refine ⟨12567030771859688697567875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378020514573125798378583 12567030771859688697567875)
        ·
          refine ⟨18850546157789533046351813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567030771859688697567875 18850546157789533046351813)
          ·
            refine ⟨3534477404585537446190965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18850546157789533046351813 3534477404585537446190965)
            ·
              refine ⟨331357256679894135580403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3534477404585537446190965 331357256679894135580403)
              ·
                refine ⟨497035885019841203370605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331357256679894135580403 497035885019841203370605)
                ·
                  refine ⟨186388456882440451263977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497035885019841203370605 186388456882440451263977)
                  ·
                    rfl

theorem cell20_408364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_408364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408364 prefixEnd_408364 := by exact prefixLift 408364
  have htrace : WordTrace (prefixWord ++ tailWord_408364) baseStart_408364 baseEnd_408364 := by
    simpa [prefixWord, tailWord_408364, baseEnd_408364] using wordTrace_append hprefix tailTrace_408364
  have hstable : (prefixWord ++ tailWord_408364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408364).length < 2 ^ (prefixWord ++ tailWord_408364).sum := by decide
  have hdescent : baseEnd_408364 < baseStart_408364 := by decide
  rcases family_descends (prefixWord ++ tailWord_408364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408378 : List Nat := [3, 1, 1, 1, 6, 1, 1, 6]
def baseStart_408378 : Nat := 118140960795 + 408378 * 2 ^ 59
def prefixEnd_408378 : Nat := 4983230072969 + 3 ^ 40 * 408378 * 2
def baseEnd_408378 : Nat := 62131615621306208265751

theorem tailTrace_408378 : CollatzResearch.WordTrace tailWord_408378 prefixEnd_408378 62131615621306208265751 := by
  unfold tailWord_408378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723692328630931563698447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9929846209682484169862525 3723692328630931563698447)
  ·
    refine ⟨5585538492946397345547671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3723692328630931563698447 5585538492946397345547671)
    ·
      refine ⟨8378307739419596018321507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5585538492946397345547671 8378307739419596018321507)
      ·
        refine ⟨12567461609129394027482261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8378307739419596018321507 12567461609129394027482261)
        ·
          refine ⟨589099762927940345038231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12567461609129394027482261 589099762927940345038231)
          ·
            refine ⟨883649644391910517557347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589099762927940345038231 883649644391910517557347)
            ·
              refine ⟨1325474466587865776336021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883649644391910517557347 1325474466587865776336021)
              ·
                refine ⟨62131615621306208265751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1325474466587865776336021 62131615621306208265751)
                ·
                  rfl

theorem cell20_408378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_408378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408378 prefixEnd_408378 := by exact prefixLift 408378
  have htrace : WordTrace (prefixWord ++ tailWord_408378) baseStart_408378 baseEnd_408378 := by
    simpa [prefixWord, tailWord_408378, baseEnd_408378] using wordTrace_append hprefix tailTrace_408378
  have hstable : (prefixWord ++ tailWord_408378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408378).length < 2 ^ (prefixWord ++ tailWord_408378).sum := by decide
  have hdescent : baseEnd_408378 < baseStart_408378 := by decide
  rcases family_descends (prefixWord ++ tailWord_408378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408409 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 4]
def baseStart_408409 : Nat := 118140960795 + 408409 * 2 ^ 59
def prefixEnd_408409 : Nat := 4983230072969 + 3 ^ 40 * 408409 * 2
def baseEnd_408409 : Nat := 186408996108620294763793

theorem tailTrace_408409 : CollatzResearch.WordTrace tailWord_408409 prefixEnd_408409 186408996108620294763793 := by
  unfold tailWord_408409
  simp only [CollatzResearch.WordTrace]
  refine ⟨14895899977411418549172281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9930599984940945699448187 14895899977411418549172281)
  ·
    refine ⟨11171924983058563911879211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14895899977411418549172281 11171924983058563911879211)
    ·
      refine ⟨16757887474587845867818817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11171924983058563911879211 16757887474587845867818817)
      ·
        refine ⟨12568415605940884400864113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16757887474587845867818817 12568415605940884400864113)
        ·
          refine ⟨9426311704455663300648085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12568415605940884400864113 9426311704455663300648085)
          ·
            refine ⟨441858361146359217217879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9426311704455663300648085 441858361146359217217879)
            ·
              refine ⟨662787541719538825826819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441858361146359217217879 662787541719538825826819)
              ·
                refine ⟨994181312579308238740229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662787541719538825826819 994181312579308238740229)
                ·
                  refine ⟨186408996108620294763793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 994181312579308238740229 186408996108620294763793)
                  ·
                    rfl

theorem cell20_408409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_408409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408409 prefixEnd_408409 := by exact prefixLift 408409
  have htrace : WordTrace (prefixWord ++ tailWord_408409) baseStart_408409 baseEnd_408409 := by
    simpa [prefixWord, tailWord_408409, baseEnd_408409] using wordTrace_append hprefix tailTrace_408409
  have hstable : (prefixWord ++ tailWord_408409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408409).length < 2 ^ (prefixWord ++ tailWord_408409).sum := by decide
  have hdescent : baseEnd_408409 < baseStart_408409 := by decide
  rcases family_descends (prefixWord ++ tailWord_408409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408419 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 3]
def baseStart_408419 : Nat := 118140960795 + 408419 * 2 ^ 59
def prefixEnd_408419 : Nat := 4983230072969 + 3 ^ 40 * 408419 * 2
def baseEnd_408419 : Nat := 186413560381104704430419

theorem tailTrace_408419 : CollatzResearch.WordTrace tailWord_408419 prefixEnd_408419 186413560381104704430419 := by
  unfold tailWord_408419
  simp only [CollatzResearch.WordTrace]
  refine ⟨14896264707375190257036311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9930843138250126838024207 14896264707375190257036311)
  ·
    refine ⟨22344397061062785385554467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14896264707375190257036311 22344397061062785385554467)
    ·
      refine ⟨33516595591594178078331701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22344397061062785385554467 33516595591594178078331701)
      ·
        refine ⟨3142180836711954194843597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33516595591594178078331701 3142180836711954194843597)
        ·
          refine ⟨1178317813766982823066349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3142180836711954194843597 1178317813766982823066349)
          ·
            refine ⟨441869180162618558649881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1178317813766982823066349 441869180162618558649881)
            ·
              refine ⟨331401885121963918987411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441869180162618558649881 331401885121963918987411)
              ·
                refine ⟨497102827682945878481117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331401885121963918987411 497102827682945878481117)
                ·
                  refine ⟨186413560381104704430419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497102827682945878481117 186413560381104704430419)
                  ·
                    rfl

theorem cell20_408419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_408419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408419 prefixEnd_408419 := by exact prefixLift 408419
  have htrace : WordTrace (prefixWord ++ tailWord_408419) baseStart_408419 baseEnd_408419 := by
    simpa [prefixWord, tailWord_408419, baseEnd_408419] using wordTrace_append hprefix tailTrace_408419
  have hstable : (prefixWord ++ tailWord_408419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408419).length < 2 ^ (prefixWord ++ tailWord_408419).sum := by decide
  have hdescent : baseEnd_408419 < baseStart_408419 := by decide
  rcases family_descends (prefixWord ++ tailWord_408419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408444 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_408444 : Nat := 118140960795 + 408444 * 2 ^ 59
def prefixEnd_408444 : Nat := 4983230072969 + 3 ^ 40 * 408444 * 2
def baseEnd_408444 : Nat := 186424971062315728596983

theorem tailTrace_408444 : CollatzResearch.WordTrace tailWord_408444 prefixEnd_408444 186424971062315728596983 := by
  unfold tailWord_408444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448588266142309763348193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9931451021523079684464257 7448588266142309763348193)
  ·
    refine ⟨5586441199606732322511145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7448588266142309763348193 5586441199606732322511145)
    ·
      refine ⟨4189830899705049241883359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5586441199606732322511145 4189830899705049241883359)
      ·
        refine ⟨6284746349557573862825039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189830899705049241883359 6284746349557573862825039)
        ·
          refine ⟨9427119524336360794237559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284746349557573862825039 9427119524336360794237559)
          ·
            refine ⟨14140679286504541191356339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9427119524336360794237559 14140679286504541191356339)
            ·
              refine ⟨21211018929756811787034509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14140679286504541191356339 21211018929756811787034509)
              ·
                refine ⟨7954132098658804420137941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21211018929756811787034509 7954132098658804420137941)
                ·
                  refine ⟨186424971062315728596983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7954132098658804420137941 186424971062315728596983)
                  ·
                    rfl

theorem cell20_408444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_408444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408444 prefixEnd_408444 := by exact prefixLift 408444
  have htrace : WordTrace (prefixWord ++ tailWord_408444) baseStart_408444 baseEnd_408444 := by
    simpa [prefixWord, tailWord_408444, baseEnd_408444] using wordTrace_append hprefix tailTrace_408444
  have hstable : (prefixWord ++ tailWord_408444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408444).length < 2 ^ (prefixWord ++ tailWord_408444).sum := by decide
  have hdescent : baseEnd_408444 < baseStart_408444 := by decide
  rcases family_descends (prefixWord ++ tailWord_408444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408450 : List Nat := [3, 4, 2, 2, 2, 7]
def baseStart_408450 : Nat := 118140960795 + 408450 * 2 ^ 59
def prefixEnd_408450 : Nat := 4983230072969 + 3 ^ 40 * 408450 * 2
def baseEnd_408450 : Nat := 6904729986140976829517

theorem tailTrace_408450 : CollatzResearch.WordTrace tailWord_408450 prefixEnd_408450 6904729986140976829517 := by
  unfold tailWord_408450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724348842565720637853701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9931596913508588367609869 3724348842565720637853701)
  ·
    refine ⟨698315407981072619597569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3724348842565720637853701 698315407981072619597569)
    ·
      refine ⟨523736555985804464698177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 698315407981072619597569 523736555985804464698177)
      ·
        refine ⟨392802416989353348523633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523736555985804464698177 392802416989353348523633)
        ·
          refine ⟨294601812742015011392725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392802416989353348523633 294601812742015011392725)
          ·
            refine ⟨6904729986140976829517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 294601812742015011392725 6904729986140976829517)
            ·
              rfl

theorem cell20_408450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 7].length) (baseStart_408450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408450 prefixEnd_408450 := by exact prefixLift 408450
  have htrace : WordTrace (prefixWord ++ tailWord_408450) baseStart_408450 baseEnd_408450 := by
    simpa [prefixWord, tailWord_408450, baseEnd_408450] using wordTrace_append hprefix tailTrace_408450
  have hstable : (prefixWord ++ tailWord_408450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408450).length < 2 ^ (prefixWord ++ tailWord_408450).sum := by decide
  have hdescent : baseEnd_408450 < baseStart_408450 := by decide
  rcases family_descends (prefixWord ++ tailWord_408450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408523 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 2]
def baseStart_408523 : Nat := 118140960795 + 408523 * 2 ^ 59
def prefixEnd_408523 : Nat := 4983230072969 + 3 ^ 40 * 408523 * 2
def baseEnd_408523 : Nat := 186461028814942564963327

theorem tailTrace_408523 : CollatzResearch.WordTrace tailWord_408523 prefixEnd_408523 186461028814942564963327 := by
  unfold tailWord_408523
  simp only [CollatzResearch.WordTrace]
  refine ⟨14900057898998416018822223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9933371932665610679214815 14900057898998416018822223)
  ·
    refine ⟨22350086848497624028233335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14900057898998416018822223 22350086848497624028233335)
    ·
      refine ⟨33525130272746436042350003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22350086848497624028233335 33525130272746436042350003)
      ·
        refine ⟨50287695409119654063525005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33525130272746436042350003 50287695409119654063525005)
        ·
          refine ⟨18857885778419870273821877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50287695409119654063525005 18857885778419870273821877)
          ·
            refine ⟨1767926791726862838170801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18857885778419870273821877 1767926791726862838170801)
            ·
              refine ⟨1325945093795147128628101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767926791726862838170801 1325945093795147128628101)
              ·
                refine ⟨248614705086590086617769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1325945093795147128628101 248614705086590086617769)
                ·
                  refine ⟨186461028814942564963327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248614705086590086617769 186461028814942564963327)
                  ·
                    rfl

theorem cell20_408523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 2].length) (baseStart_408523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408523 prefixEnd_408523 := by exact prefixLift 408523
  have htrace : WordTrace (prefixWord ++ tailWord_408523) baseStart_408523 baseEnd_408523 := by
    simpa [prefixWord, tailWord_408523, baseEnd_408523] using wordTrace_append hprefix tailTrace_408523
  have hstable : (prefixWord ++ tailWord_408523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408523).length < 2 ^ (prefixWord ++ tailWord_408523).sum := by decide
  have hdescent : baseEnd_408523 < baseStart_408523 := by decide
  rcases family_descends (prefixWord ++ tailWord_408523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408533 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 3]
def baseStart_408533 : Nat := 118140960795 + 408533 * 2 ^ 59
def prefixEnd_408533 : Nat := 4983230072969 + 3 ^ 40 * 408533 * 2
def baseEnd_408533 : Nat := 186465593087426974629953

theorem tailTrace_408533 : CollatzResearch.WordTrace tailWord_408533 prefixEnd_408533 186465593087426974629953 := by
  unfold tailWord_408533
  simp only [CollatzResearch.WordTrace]
  refine ⟨14900422628962187726686253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9933615085974791817790835 14900422628962187726686253)
  ·
    refine ⟨5587658485860820397507345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14900422628962187726686253 5587658485860820397507345)
    ·
      refine ⟨4190743864395615298130509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5587658485860820397507345 4190743864395615298130509)
      ·
        refine ⟨1571528949148355736798941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4190743864395615298130509 1571528949148355736798941)
        ·
          refine ⟨589323355930633401299603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1571528949148355736798941 589323355930633401299603)
          ·
            refine ⟨883985033895950101949405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589323355930633401299603 883985033895950101949405)
            ·
              refine ⟨331494387710981288231027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883985033895950101949405 331494387710981288231027)
              ·
                refine ⟨497241581566471932346541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331494387710981288231027 497241581566471932346541)
                ·
                  refine ⟨186465593087426974629953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497241581566471932346541 186465593087426974629953)
                  ·
                    rfl

theorem cell20_408533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_408533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408533 prefixEnd_408533 := by exact prefixLift 408533
  have htrace : WordTrace (prefixWord ++ tailWord_408533) baseStart_408533 baseEnd_408533 := by
    simpa [prefixWord, tailWord_408533, baseEnd_408533] using wordTrace_append hprefix tailTrace_408533
  have hstable : (prefixWord ++ tailWord_408533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408533).length < 2 ^ (prefixWord ++ tailWord_408533).sum := by decide
  have hdescent : baseEnd_408533 < baseStart_408533 := by decide
  rcases family_descends (prefixWord ++ tailWord_408533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408574 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_408574 : Nat := 118140960795 + 408574 * 2 ^ 59
def prefixEnd_408574 : Nat := 4983230072969 + 3 ^ 40 * 408574 * 2
def baseEnd_408574 : Nat := 186484306604613054263119

theorem tailTrace_408574 : CollatzResearch.WordTrace tailWord_408574 prefixEnd_408574 186484306604613054263119 := by
  unfold tailWord_408574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862739752726706466116097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9934612014542434485952517 1862739752726706466116097)
  ·
    refine ⟨1397054814545029849587073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1862739752726706466116097 1397054814545029849587073)
    ·
      refine ⟨1047791110908772387190305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397054814545029849587073 1047791110908772387190305)
      ·
        refine ⟨785843333181579290392729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1047791110908772387190305 785843333181579290392729)
        ·
          refine ⟨589382499886184467794547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785843333181579290392729 589382499886184467794547)
          ·
            refine ⟨884073749829276701691821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589382499886184467794547 884073749829276701691821)
            ·
              refine ⟨331527656185978763134433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884073749829276701691821 331527656185978763134433)
              ·
                refine ⟨248645742139484072350825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331527656185978763134433 248645742139484072350825)
                ·
                  refine ⟨186484306604613054263119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248645742139484072350825 186484306604613054263119)
                  ·
                    rfl

theorem cell20_408574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_408574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408574 prefixEnd_408574 := by exact prefixLift 408574
  have htrace : WordTrace (prefixWord ++ tailWord_408574) baseStart_408574 baseEnd_408574 := by
    simpa [prefixWord, tailWord_408574, baseEnd_408574] using wordTrace_append hprefix tailTrace_408574
  have hstable : (prefixWord ++ tailWord_408574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408574).length < 2 ^ (prefixWord ++ tailWord_408574).sum := by decide
  have hdescent : baseEnd_408574 < baseStart_408574 := by decide
  rcases family_descends (prefixWord ++ tailWord_408574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408630 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_408630 : Nat := 118140960795 + 408630 * 2 ^ 59
def prefixEnd_408630 : Nat := 4983230072969 + 3 ^ 40 * 408630 * 2
def baseEnd_408630 : Nat := 186509866530525748396223

theorem tailTrace_408630 : CollatzResearch.WordTrace tailWord_408630 prefixEnd_408630 186509866530525748396223 := by
  unfold tailWord_408630
  simp only [CollatzResearch.WordTrace]
  refine ⟨931497531850673330810459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9935973673073848861978229 931497531850673330810459)
  ·
    refine ⟨1397246297776009996215689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 931497531850673330810459 1397246297776009996215689)
    ·
      refine ⟨1047934723332007497161767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397246297776009996215689 1047934723332007497161767)
      ·
        refine ⟨1571902084998011245742651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047934723332007497161767 1571902084998011245742651)
        ·
          refine ⟨2357853127497016868613977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1571902084998011245742651 2357853127497016868613977)
          ·
            refine ⟨1768389845622762651460483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2357853127497016868613977 1768389845622762651460483)
            ·
              refine ⟨2652584768434143977190725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768389845622762651460483 2652584768434143977190725)
              ·
                refine ⟨497359644081401995723261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2652584768434143977190725 497359644081401995723261)
                ·
                  refine ⟨186509866530525748396223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497359644081401995723261 186509866530525748396223)
                  ·
                    rfl

theorem cell20_408630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_408630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408630 prefixEnd_408630 := by exact prefixLift 408630
  have htrace : WordTrace (prefixWord ++ tailWord_408630) baseStart_408630 baseEnd_408630 := by
    simpa [prefixWord, tailWord_408630, baseEnd_408630] using wordTrace_append hprefix tailTrace_408630
  have hstable : (prefixWord ++ tailWord_408630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408630).length < 2 ^ (prefixWord ++ tailWord_408630).sum := by decide
  have hdescent : baseEnd_408630 < baseStart_408630 := by decide
  rcases family_descends (prefixWord ++ tailWord_408630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408633 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 2]
def baseStart_408633 : Nat := 118140960795 + 408633 * 2 ^ 59
def prefixEnd_408633 : Nat := 4983230072969 + 3 ^ 40 * 408633 * 2
def baseEnd_408633 : Nat := 186511235812271071296211

theorem tailTrace_408633 : CollatzResearch.WordTrace tailWord_408633 prefixEnd_408633 186511235812271071296211 := by
  unfold tailWord_408633
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904069928599904805326553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9936046619066603203551035 14904069928599904805326553)
  ·
    refine ⟨11178052446449928603994915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14904069928599904805326553 11178052446449928603994915)
    ·
      refine ⟨16767078669674892905992373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178052446449928603994915 16767078669674892905992373)
      ·
        refine ⟨1571913625282021209936785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16767078669674892905992373 1571913625282021209936785)
        ·
          refine ⟨1178935218961515907452589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571913625282021209936785 1178935218961515907452589)
          ·
            refine ⟨442100707110568465294721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1178935218961515907452589 442100707110568465294721)
            ·
              refine ⟨331575530332926348971041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442100707110568465294721 331575530332926348971041)
              ·
                refine ⟨248681647749694761728281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331575530332926348971041 248681647749694761728281)
                ·
                  refine ⟨186511235812271071296211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248681647749694761728281 186511235812271071296211)
                  ·
                    rfl

theorem cell20_408633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_408633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408633 prefixEnd_408633 := by exact prefixLift 408633
  have htrace : WordTrace (prefixWord ++ tailWord_408633) baseStart_408633 baseEnd_408633 := by
    simpa [prefixWord, tailWord_408633, baseEnd_408633] using wordTrace_append hprefix tailTrace_408633
  have hstable : (prefixWord ++ tailWord_408633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408633).length < 2 ^ (prefixWord ++ tailWord_408633).sum := by decide
  have hdescent : baseEnd_408633 < baseStart_408633 := by decide
  rcases family_descends (prefixWord ++ tailWord_408633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408634 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_408634 : Nat := 118140960795 + 408634 * 2 ^ 59
def prefixEnd_408634 : Nat := 4983230072969 + 3 ^ 40 * 408634 * 2
def baseEnd_408634 : Nat := 186511692239519512262873

theorem tailTrace_408634 : CollatzResearch.WordTrace tailWord_408634 prefixEnd_408634 186511692239519512262873 := by
  unfold tailWord_408634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726026600399070494028239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9936070934397521317408637 3726026600399070494028239)
  ·
    refine ⟨5589039900598605741042359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3726026600399070494028239 5589039900598605741042359)
    ·
      refine ⟨8383559850897908611563539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5589039900598605741042359 8383559850897908611563539)
      ·
        refine ⟨12575339776346862917345309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383559850897908611563539 12575339776346862917345309)
        ·
          refine ⟨4715752416130073594004491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12575339776346862917345309 4715752416130073594004491)
          ·
            refine ⟨7073628624195110391006737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715752416130073594004491 7073628624195110391006737)
            ·
              refine ⟨5305221468146332793255053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7073628624195110391006737 5305221468146332793255053)
              ·
                refine ⟨1989458050554874797470645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5305221468146332793255053 1989458050554874797470645)
                ·
                  refine ⟨186511692239519512262873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1989458050554874797470645 186511692239519512262873)
                  ·
                    rfl

theorem cell20_408634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_408634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408634 prefixEnd_408634 := by exact prefixLift 408634
  have htrace : WordTrace (prefixWord ++ tailWord_408634) baseStart_408634 baseEnd_408634 := by
    simpa [prefixWord, tailWord_408634, baseEnd_408634] using wordTrace_append hprefix tailTrace_408634
  have hstable : (prefixWord ++ tailWord_408634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408634).length < 2 ^ (prefixWord ++ tailWord_408634).sum := by decide
  have hdescent : baseEnd_408634 < baseStart_408634 := by decide
  rcases family_descends (prefixWord ++ tailWord_408634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408658 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_408658 : Nat := 118140960795 + 408658 * 2 ^ 59
def prefixEnd_408658 : Nat := 4983230072969 + 3 ^ 40 * 408658 * 2
def baseEnd_408658 : Nat := 186522646493482095462775

theorem tailTrace_408658 : CollatzResearch.WordTrace tailWord_408658 prefixEnd_408658 186522646493482095462775 := by
  unfold tailWord_408658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726245438377333518746657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9936654502339556049991085 3726245438377333518746657)
  ·
    refine ⟨2794684078783000139059993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3726245438377333518746657 2794684078783000139059993)
    ·
      refine ⟨2096013059087250104294995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2794684078783000139059993 2096013059087250104294995)
      ·
        refine ⟨3144019588630875156442493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096013059087250104294995 3144019588630875156442493)
        ·
          refine ⟨1179007345736578183665935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3144019588630875156442493 1179007345736578183665935)
          ·
            refine ⟨1768511018604867275498903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179007345736578183665935 1768511018604867275498903)
            ·
              refine ⟨2652766527907300913248355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768511018604867275498903 2652766527907300913248355)
              ·
                refine ⟨3979149791860951369872533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652766527907300913248355 3979149791860951369872533)
                ·
                  refine ⟨186522646493482095462775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3979149791860951369872533 186522646493482095462775)
                  ·
                    rfl

theorem cell20_408658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_408658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408658 prefixEnd_408658 := by exact prefixLift 408658
  have htrace : WordTrace (prefixWord ++ tailWord_408658) baseStart_408658 baseEnd_408658 := by
    simpa [prefixWord, tailWord_408658, baseEnd_408658] using wordTrace_append hprefix tailTrace_408658
  have hstable : (prefixWord ++ tailWord_408658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408658).length < 2 ^ (prefixWord ++ tailWord_408658).sum := by decide
  have hdescent : baseEnd_408658 < baseStart_408658 := by decide
  rcases family_descends (prefixWord ++ tailWord_408658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408672 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_408672 : Nat := 118140960795 + 408672 * 2 ^ 59
def prefixEnd_408672 : Nat := 4983230072969 + 3 ^ 40 * 408672 * 2
def baseEnd_408672 : Nat := 186529036474960268996051

theorem tailTrace_408672 : CollatzResearch.WordTrace tailWord_408672 prefixEnd_408672 186529036474960268996051 := by
  unfold tailWord_408672
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452746187729307232998135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9936994916972409643997513 7452746187729307232998135)
  ·
    refine ⟨11179119281593960849497203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452746187729307232998135 11179119281593960849497203)
    ·
      refine ⟨16768678922390941274245805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11179119281593960849497203 16768678922390941274245805)
      ·
        refine ⟨6288254595896602977842177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16768678922390941274245805 6288254595896602977842177)
        ·
          refine ⟨4716190946922452233381633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6288254595896602977842177 4716190946922452233381633)
          ·
            refine ⟨3537143210191839175036225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716190946922452233381633 3537143210191839175036225)
            ·
              refine ⟨2652857407643879381277169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3537143210191839175036225 2652857407643879381277169)
              ·
                refine ⟨1989643055732909535957877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652857407643879381277169 1989643055732909535957877)
                ·
                  refine ⟨186529036474960268996051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1989643055732909535957877 186529036474960268996051)
                  ·
                    rfl

theorem cell20_408672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_408672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408672 prefixEnd_408672 := by exact prefixLift 408672
  have htrace : WordTrace (prefixWord ++ tailWord_408672) baseStart_408672 baseEnd_408672 := by
    simpa [prefixWord, tailWord_408672, baseEnd_408672] using wordTrace_append hprefix tailTrace_408672
  have hstable : (prefixWord ++ tailWord_408672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408672).length < 2 ^ (prefixWord ++ tailWord_408672).sum := by decide
  have hdescent : baseEnd_408672 < baseStart_408672 := by decide
  rcases family_descends (prefixWord ++ tailWord_408672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408730 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_408730 : Nat := 118140960795 + 408730 * 2 ^ 59
def prefixEnd_408730 : Nat := 4983230072969 + 3 ^ 40 * 408730 * 2
def baseEnd_408730 : Nat := 186555509255369845062481

theorem tailTrace_408730 : CollatzResearch.WordTrace tailWord_408730 prefixEnd_408730 186555509255369845062481 := by
  unfold tailWord_408730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726901952312122592901911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9938405206165660247738429 3726901952312122592901911)
  ·
    refine ⟨5590352928468183889352867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3726901952312122592901911 5590352928468183889352867)
    ·
      refine ⟨8385529392702275834029301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590352928468183889352867 8385529392702275834029301)
      ·
        refine ⟨786143380565838359440247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8385529392702275834029301 786143380565838359440247)
        ·
          refine ⟨1179215070848757539160371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786143380565838359440247 1179215070848757539160371)
          ·
            refine ⟨1768822606273136308740557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179215070848757539160371 1768822606273136308740557)
            ·
              refine ⟨663308477352426115777709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1768822606273136308740557 663308477352426115777709)
              ·
                refine ⟨248740679007159793416641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663308477352426115777709 248740679007159793416641)
                ·
                  refine ⟨186555509255369845062481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248740679007159793416641 186555509255369845062481)
                  ·
                    rfl

theorem cell20_408730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_408730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408730 prefixEnd_408730 := by exact prefixLift 408730
  have htrace : WordTrace (prefixWord ++ tailWord_408730) baseStart_408730 baseEnd_408730 := by
    simpa [prefixWord, tailWord_408730, baseEnd_408730] using wordTrace_append hprefix tailTrace_408730
  have hstable : (prefixWord ++ tailWord_408730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408730).length < 2 ^ (prefixWord ++ tailWord_408730).sum := by decide
  have hdescent : baseEnd_408730 < baseStart_408730 := by decide
  rcases family_descends (prefixWord ++ tailWord_408730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408741 : List Nat := [1, 3, 1, 2, 1, 6, 6]
def baseStart_408741 : Nat := 118140960795 + 408741 * 2 ^ 59
def prefixEnd_408741 : Nat := 4983230072969 + 3 ^ 40 * 408741 * 2
def baseEnd_408741 : Nat := 20728947772789188410641

theorem tailTrace_408741 : CollatzResearch.WordTrace tailWord_408741 prefixEnd_408741 20728947772789188410641 := by
  unfold tailWord_408741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908009012208639250258077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9938672674805759500172051 14908009012208639250258077)
  ·
    refine ⟨5590503379578239718846779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14908009012208639250258077 5590503379578239718846779)
    ·
      refine ⟨8385755069367359578270169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590503379578239718846779 8385755069367359578270169)
      ·
        refine ⟨6289316302025519683702627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8385755069367359578270169 6289316302025519683702627)
        ·
          refine ⟨9433974453038279525553941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6289316302025519683702627 9433974453038279525553941)
          ·
            refine ⟨442217552486169352760341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9433974453038279525553941 442217552486169352760341)
            ·
              refine ⟨20728947772789188410641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 442217552486169352760341 20728947772789188410641)
              ·
                rfl

theorem cell20_408741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_408741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408741 prefixEnd_408741 := by exact prefixLift 408741
  have htrace : WordTrace (prefixWord ++ tailWord_408741) baseStart_408741 baseEnd_408741 := by
    simpa [prefixWord, tailWord_408741, baseEnd_408741] using wordTrace_append hprefix tailTrace_408741
  have hstable : (prefixWord ++ tailWord_408741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408741).length < 2 ^ (prefixWord ++ tailWord_408741).sum := by decide
  have hdescent : baseEnd_408741 < baseStart_408741 := by decide
  rcases family_descends (prefixWord ++ tailWord_408741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408800 : List Nat := [2, 1, 1, 3, 1, 12]
def baseStart_408800 : Nat := 118140960795 + 408800 * 2 ^ 59
def prefixEnd_408800 : Nat := 4983230072969 + 3 ^ 40 * 408800 * 2
def baseEnd_408800 : Nat := 6910646635657804175143

theorem tailTrace_408800 : CollatzResearch.WordTrace tailWord_408800 prefixEnd_408800 6910646635657804175143 := by
  unfold tailWord_408800
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455080459497446163327927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9940107279329928217770569 7455080459497446163327927)
  ·
    refine ⟨11182620689246169244991891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7455080459497446163327927 11182620689246169244991891)
    ·
      refine ⟨16773931033869253867487837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11182620689246169244991891 16773931033869253867487837)
      ·
        refine ⟨6290224137700970200307939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16773931033869253867487837 6290224137700970200307939)
        ·
          refine ⟨9435336206551455300461909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6290224137700970200307939 9435336206551455300461909)
          ·
            refine ⟨6910646635657804175143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9435336206551455300461909 6910646635657804175143)
            ·
              rfl

theorem cell20_408800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 12].length) (baseStart_408800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408800 prefixEnd_408800 := by exact prefixLift 408800
  have htrace : WordTrace (prefixWord ++ tailWord_408800) baseStart_408800 baseEnd_408800 := by
    simpa [prefixWord, tailWord_408800, baseEnd_408800] using wordTrace_append hprefix tailTrace_408800
  have hstable : (prefixWord ++ tailWord_408800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408800).length < 2 ^ (prefixWord ++ tailWord_408800).sum := by decide
  have hdescent : baseEnd_408800 < baseStart_408800 := by decide
  rcases family_descends (prefixWord ++ tailWord_408800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408831 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_408831 : Nat := 118140960795 + 408831 * 2 ^ 59
def prefixEnd_408831 : Nat := 4983230072969 + 3 ^ 40 * 408831 * 2
def baseEnd_408831 : Nat := 186601608407462382695401

theorem tailTrace_408831 : CollatzResearch.WordTrace tailWord_408831 prefixEnd_408831 186601608407462382695401 := by
  unfold tailWord_408831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14911291581882584621034347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9940861054588389747356231 14911291581882584621034347)
  ·
    refine ⟨22366937372823876931551521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14911291581882584621034347 22366937372823876931551521)
    ·
      refine ⟨16775203029617907698663641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22366937372823876931551521 16775203029617907698663641)
      ·
        refine ⟨12581402272213430773997731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16775203029617907698663641 12581402272213430773997731)
        ·
          refine ⟨18872103408320146160996597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12581402272213430773997731 18872103408320146160996597)
          ·
            refine ⟨1769259694530013702593431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18872103408320146160996597 1769259694530013702593431)
            ·
              refine ⟨2653889541795020553890147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769259694530013702593431 2653889541795020553890147)
              ·
                refine ⟨3980834312692530830835221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653889541795020553890147 3980834312692530830835221)
                ·
                  refine ⟨186601608407462382695401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3980834312692530830835221 186601608407462382695401)
                  ·
                    rfl

theorem cell20_408831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_408831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408831 prefixEnd_408831 := by exact prefixLift 408831
  have htrace : WordTrace (prefixWord ++ tailWord_408831) baseStart_408831 baseEnd_408831 := by
    simpa [prefixWord, tailWord_408831, baseEnd_408831] using wordTrace_append hprefix tailTrace_408831
  have hstable : (prefixWord ++ tailWord_408831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408831).length < 2 ^ (prefixWord ++ tailWord_408831).sum := by decide
  have hdescent : baseEnd_408831 < baseStart_408831 := by decide
  rcases family_descends (prefixWord ++ tailWord_408831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408858 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_408858 : Nat := 118140960795 + 408858 * 2 ^ 59
def prefixEnd_408858 : Nat := 4983230072969 + 3 ^ 40 * 408858 * 2
def baseEnd_408858 : Nat := 186613931943170288795291

theorem tailTrace_408858 : CollatzResearch.WordTrace tailWord_408858 prefixEnd_408858 186613931943170288795291 := by
  unfold tailWord_408858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728069088196192058066807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9941517568523178821511485 3728069088196192058066807)
  ·
    refine ⟨5592103632294288087100211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3728069088196192058066807 5592103632294288087100211)
    ·
      refine ⟨8388155448441432130650317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5592103632294288087100211 8388155448441432130650317)
      ·
        refine ⟨3145558293165537048993869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8388155448441432130650317 3145558293165537048993869)
        ·
          refine ⟨1179584359937076393372701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3145558293165537048993869 1179584359937076393372701)
          ·
            refine ⟨442344134976403647514763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1179584359937076393372701 442344134976403647514763)
            ·
              refine ⟨663516202464605471272145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442344134976403647514763 663516202464605471272145)
              ·
                refine ⟨497637151848454103454109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663516202464605471272145 497637151848454103454109)
                ·
                  refine ⟨186613931943170288795291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497637151848454103454109 186613931943170288795291)
                  ·
                    rfl

theorem cell20_408858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_408858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408858 prefixEnd_408858 := by exact prefixLift 408858
  have htrace : WordTrace (prefixWord ++ tailWord_408858) baseStart_408858 baseEnd_408858 := by
    simpa [prefixWord, tailWord_408858, baseEnd_408858] using wordTrace_append hprefix tailTrace_408858
  have hstable : (prefixWord ++ tailWord_408858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408858).length < 2 ^ (prefixWord ++ tailWord_408858).sum := by decide
  have hdescent : baseEnd_408858 < baseStart_408858 := by decide
  rcases family_descends (prefixWord ++ tailWord_408858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408876 : List Nat := [2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_408876 : Nat := 118140960795 + 408876 * 2 ^ 59
def prefixEnd_408876 : Nat := 4983230072969 + 3 ^ 40 * 408876 * 2
def baseEnd_408876 : Nat := 62207382544547408731739

theorem tailTrace_408876 : CollatzResearch.WordTrace tailWord_408876 prefixEnd_408876 62207382544547408731739 := by
  unfold tailWord_408876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456466433359778653211241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9941955244479704870948321 7456466433359778653211241)
  ·
    refine ⟨5592349825019833989908431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7456466433359778653211241 5592349825019833989908431)
    ·
      refine ⟨8388524737529750984862647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5592349825019833989908431 8388524737529750984862647)
      ·
        refine ⟨12582787106294626477293971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8388524737529750984862647 12582787106294626477293971)
        ·
          refine ⟨18874180659441939715940957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12582787106294626477293971 18874180659441939715940957)
          ·
            refine ⟨7077817747290727393477859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18874180659441939715940957 7077817747290727393477859)
            ·
              refine ⟨10616726620936091090216789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7077817747290727393477859 10616726620936091090216789)
              ·
                refine ⟨62207382544547408731739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10616726620936091090216789 62207382544547408731739)
                ·
                  rfl

theorem cell20_408876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_408876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408876 prefixEnd_408876 := by exact prefixLift 408876
  have htrace : WordTrace (prefixWord ++ tailWord_408876) baseStart_408876 baseEnd_408876 := by
    simpa [prefixWord, tailWord_408876, baseEnd_408876] using wordTrace_append hprefix tailTrace_408876
  have hstable : (prefixWord ++ tailWord_408876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408876).length < 2 ^ (prefixWord ++ tailWord_408876).sum := by decide
  have hdescent : baseEnd_408876 < baseStart_408876 := by decide
  rcases family_descends (prefixWord ++ tailWord_408876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408889 : List Nat := [1, 2, 1, 6, 2, 2, 2, 4]
def baseStart_408889 : Nat := 118140960795 + 408889 * 2 ^ 59
def prefixEnd_408889 : Nat := 4983230072969 + 3 ^ 40 * 408889 * 2
def baseEnd_408889 : Nat := 62209360395957319587277

theorem tailTrace_408889 : CollatzResearch.WordTrace tailWord_408889 prefixEnd_408889 62209360395957319587277 := by
  unfold tailWord_408889
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913407015672460526645721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9942271343781640351097147 14913407015672460526645721)
  ·
    refine ⟨11185055261754345394984291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14913407015672460526645721 11185055261754345394984291)
    ·
      refine ⟨16777582892631518092476437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11185055261754345394984291 16777582892631518092476437)
      ·
        refine ⟨786449198092102410584833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16777582892631518092476437 786449198092102410584833)
        ·
          refine ⟨589836898569076807938625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786449198092102410584833 589836898569076807938625)
          ·
            refine ⟨442377673926807605953969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589836898569076807938625 442377673926807605953969)
            ·
              refine ⟨331783255445105704465477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442377673926807605953969 331783255445105704465477)
              ·
                refine ⟨62209360395957319587277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331783255445105704465477 62209360395957319587277)
                ·
                  rfl

theorem cell20_408889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 4].length) (baseStart_408889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408889 prefixEnd_408889 := by exact prefixLift 408889
  have htrace : WordTrace (prefixWord ++ tailWord_408889) baseStart_408889 baseEnd_408889 := by
    simpa [prefixWord, tailWord_408889, baseEnd_408889] using wordTrace_append hprefix tailTrace_408889
  have hstable : (prefixWord ++ tailWord_408889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408889).length < 2 ^ (prefixWord ++ tailWord_408889).sum := by decide
  have hdescent : baseEnd_408889 < baseStart_408889 := by decide
  rcases family_descends (prefixWord ++ tailWord_408889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408903 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 2]
def baseStart_408903 : Nat := 118140960795 + 408903 * 2 ^ 59
def prefixEnd_408903 : Nat := 4983230072969 + 3 ^ 40 * 408903 * 2
def baseEnd_408903 : Nat := 186634471169350132295107

theorem tailTrace_408903 : CollatzResearch.WordTrace tailWord_408903 prefixEnd_408903 186634471169350132295107 := by
  unfold tailWord_408903
  simp only [CollatzResearch.WordTrace]
  refine ⟨14913917637621740917655363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9942611758414493945103575 14913917637621740917655363)
  ·
    refine ⟨22370876456432611376483045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14913917637621740917655363 22370876456432611376483045)
    ·
      refine ⟨4194539335581114633090571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22370876456432611376483045 4194539335581114633090571)
      ·
        refine ⟨6291809003371671949635857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4194539335581114633090571 6291809003371671949635857)
        ·
          refine ⟨4718856752528753962226893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6291809003371671949635857 4718856752528753962226893)
          ·
            refine ⟨1769571282198282735835085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4718856752528753962226893 1769571282198282735835085)
            ·
              refine ⟨663589230824356025938157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1769571282198282735835085 663589230824356025938157)
              ·
                refine ⟨248845961559133509726809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663589230824356025938157 248845961559133509726809)
                ·
                  refine ⟨186634471169350132295107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248845961559133509726809 186634471169350132295107)
                  ·
                    rfl

theorem cell20_408903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 2].length) (baseStart_408903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408903 prefixEnd_408903 := by exact prefixLift 408903
  have htrace : WordTrace (prefixWord ++ tailWord_408903) baseStart_408903 baseEnd_408903 := by
    simpa [prefixWord, tailWord_408903, baseEnd_408903] using wordTrace_append hprefix tailTrace_408903
  have hstable : (prefixWord ++ tailWord_408903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408903).length < 2 ^ (prefixWord ++ tailWord_408903).sum := by decide
  have hdescent : baseEnd_408903 < baseStart_408903 := by decide
  rcases family_descends (prefixWord ++ tailWord_408903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408931 : List Nat := [1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_408931 : Nat := 118140960795 + 408931 * 2 ^ 59
def prefixEnd_408931 : Nat := 4983230072969 + 3 ^ 40 * 408931 * 2
def baseEnd_408931 : Nat := 62215750377435493120553

theorem tailTrace_408931 : CollatzResearch.WordTrace tailWord_408931 prefixEnd_408931 62215750377435493120553 := by
  unfold tailWord_408931
  simp only [CollatzResearch.WordTrace]
  refine ⟨14914938881520301699674647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9943292587680201133116431 14914938881520301699674647)
  ·
    refine ⟨22372408322280452549511971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14914938881520301699674647 22372408322280452549511971)
    ·
      refine ⟨33558612483420678824267957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22372408322280452549511971 33558612483420678824267957)
      ·
        refine ⟨3146119920320688639775121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33558612483420678824267957 3146119920320688639775121)
        ·
          refine ⟨2359589940240516479831341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3146119920320688639775121 2359589940240516479831341)
          ·
            refine ⟨884846227590193679936753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2359589940240516479831341 884846227590193679936753)
            ·
              refine ⟨663634670692645259952565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884846227590193679936753 663634670692645259952565)
              ·
                refine ⟨62215750377435493120553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 663634670692645259952565 62215750377435493120553)
                ·
                  rfl

theorem cell20_408931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_408931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408931 prefixEnd_408931 := by exact prefixLift 408931
  have htrace : WordTrace (prefixWord ++ tailWord_408931) baseStart_408931 baseEnd_408931 := by
    simpa [prefixWord, tailWord_408931, baseEnd_408931] using wordTrace_append hprefix tailTrace_408931
  have hstable : (prefixWord ++ tailWord_408931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408931).length < 2 ^ (prefixWord ++ tailWord_408931).sum := by decide
  have hdescent : baseEnd_408931 < baseStart_408931 := by decide
  rcases family_descends (prefixWord ++ tailWord_408931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408945 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_408945 : Nat := 118140960795 + 408945 * 2 ^ 59
def prefixEnd_408945 : Nat := 4983230072969 + 3 ^ 40 * 408945 * 2
def baseEnd_408945 : Nat := 186653641113784652894935

theorem tailTrace_408945 : CollatzResearch.WordTrace tailWord_408945 prefixEnd_408945 186653641113784652894935 := by
  unfold tailWord_408945
  simp only [CollatzResearch.WordTrace]
  refine ⟨14915449503469582090684289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9943633002313054727122859 14915449503469582090684289)
  ·
    refine ⟨11186587127602186568013217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14915449503469582090684289 11186587127602186568013217)
    ·
      refine ⟨8389940345701639926009913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11186587127602186568013217 8389940345701639926009913)
      ·
        refine ⟨6292455259276229944507435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8389940345701639926009913 6292455259276229944507435)
        ·
          refine ⟨9438682888914344916761153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292455259276229944507435 9438682888914344916761153)
          ·
            refine ⟨7079012166685758687570865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438682888914344916761153 7079012166685758687570865)
            ·
              refine ⟨5309259125014319015678149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7079012166685758687570865 5309259125014319015678149)
              ·
                refine ⟨995486085940184815439653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5309259125014319015678149 995486085940184815439653)
                ·
                  refine ⟨186653641113784652894935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995486085940184815439653 186653641113784652894935)
                  ·
                    rfl

theorem cell20_408945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_408945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408945 prefixEnd_408945 := by exact prefixLift 408945
  have htrace : WordTrace (prefixWord ++ tailWord_408945) baseStart_408945 baseEnd_408945 := by
    simpa [prefixWord, tailWord_408945, baseEnd_408945] using wordTrace_append hprefix tailTrace_408945
  have hstable : (prefixWord ++ tailWord_408945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408945).length < 2 ^ (prefixWord ++ tailWord_408945).sum := by decide
  have hdescent : baseEnd_408945 < baseStart_408945 := by decide
  rcases family_descends (prefixWord ++ tailWord_408945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408969 : List Nat := [1, 2, 1, 1, 8, 7]
def baseStart_408969 : Nat := 118140960795 + 408969 * 2 ^ 59
def prefixEnd_408969 : Nat := 4983230072969 + 3 ^ 40 * 408969 * 2
def baseEnd_408969 : Nat := 6913503532138786522031

theorem tailTrace_408969 : CollatzResearch.WordTrace tailWord_408969 prefixEnd_408969 6913503532138786522031 := by
  unfold tailWord_408969
  simp only [CollatzResearch.WordTrace]
  refine ⟨14916324855382634189557961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9944216570255089459705307 14916324855382634189557961)
  ·
    refine ⟨11187243641536975642168471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14916324855382634189557961 11187243641536975642168471)
    ·
      refine ⟨16780865462305463463252707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11187243641536975642168471 16780865462305463463252707)
      ·
        refine ⟨25171298193458195194879061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16780865462305463463252707 25171298193458195194879061)
        ·
          refine ⟨294976150704588224939989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 25171298193458195194879061 294976150704588224939989)
          ·
            refine ⟨6913503532138786522031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 294976150704588224939989 6913503532138786522031)
            ·
              rfl

theorem cell20_408969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 7].length) (baseStart_408969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408969 prefixEnd_408969 := by exact prefixLift 408969
  have htrace : WordTrace (prefixWord ++ tailWord_408969) baseStart_408969 baseEnd_408969 := by
    simpa [prefixWord, tailWord_408969, baseEnd_408969] using wordTrace_append hprefix tailTrace_408969
  have hstable : (prefixWord ++ tailWord_408969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408969).length < 2 ^ (prefixWord ++ tailWord_408969).sum := by decide
  have hdescent : baseEnd_408969 < baseStart_408969 := by decide
  rcases family_descends (prefixWord ++ tailWord_408969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408983 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_408983 : Nat := 118140960795 + 408983 * 2 ^ 59
def prefixEnd_408983 : Nat := 4983230072969 + 3 ^ 40 * 408983 * 2
def baseEnd_408983 : Nat := 186670985349225409628113

theorem tailTrace_408983 : CollatzResearch.WordTrace tailWord_408983 prefixEnd_408983 186670985349225409628113 := by
  unfold tailWord_408983
  simp only [CollatzResearch.WordTrace]
  refine ⟨14916835477331914580567603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9944556984887943053711735 14916835477331914580567603)
  ·
    refine ⟨22375253215997871870851405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14916835477331914580567603 22375253215997871870851405)
    ·
      refine ⟨8390719955999201951569277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22375253215997871870851405 8390719955999201951569277)
      ·
        refine ⟨3146519983499700731838479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8390719955999201951569277 3146519983499700731838479)
        ·
          refine ⟨4719779975249551097757719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146519983499700731838479 4719779975249551097757719)
          ·
            refine ⟨7079669962874326646636579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719779975249551097757719 7079669962874326646636579)
            ·
              refine ⟨10619504944311489969954869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079669962874326646636579 10619504944311489969954869)
              ·
                refine ⟨995578588529202184683269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10619504944311489969954869 995578588529202184683269)
                ·
                  refine ⟨186670985349225409628113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 995578588529202184683269 186670985349225409628113)
                  ·
                    rfl

theorem cell20_408983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_408983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_408983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_408983 prefixEnd_408983 := by exact prefixLift 408983
  have htrace : WordTrace (prefixWord ++ tailWord_408983) baseStart_408983 baseEnd_408983 := by
    simpa [prefixWord, tailWord_408983, baseEnd_408983] using wordTrace_append hprefix tailTrace_408983
  have hstable : (prefixWord ++ tailWord_408983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408983).length < 2 ^ (prefixWord ++ tailWord_408983).sum := by decide
  have hdescent : baseEnd_408983 < baseStart_408983 := by decide
  rcases family_descends (prefixWord ++ tailWord_408983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409021 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_409021 : Nat := 118140960795 + 409021 * 2 ^ 59
def prefixEnd_409021 : Nat := 4983230072969 + 3 ^ 40 * 409021 * 2
def baseEnd_409021 : Nat := 186688329584666166361291

theorem tailTrace_409021 : CollatzResearch.WordTrace tailWord_409021 prefixEnd_409021 186688329584666166361291 := by
  unfold tailWord_409021
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918221451194247070450917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9945480967462831380300611 14918221451194247070450917)
  ·
    refine ⟨2797166522098921325709547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14918221451194247070450917 2797166522098921325709547)
    ·
      refine ⟨4195749783148381988564321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797166522098921325709547 4195749783148381988564321)
      ·
        refine ⟨3146812337361286491423241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4195749783148381988564321 3146812337361286491423241)
        ·
          refine ⟨2360109253020964868567431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3146812337361286491423241 2360109253020964868567431)
          ·
            refine ⟨3540163879531447302851147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360109253020964868567431 3540163879531447302851147)
            ·
              refine ⟨5310245819297170954276721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540163879531447302851147 5310245819297170954276721)
              ·
                refine ⟨3982684364472878215707541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310245819297170954276721 3982684364472878215707541)
                ·
                  refine ⟨186688329584666166361291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3982684364472878215707541 186688329584666166361291)
                  ·
                    rfl

theorem cell20_409021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_409021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409021 prefixEnd_409021 := by exact prefixLift 409021
  have htrace : WordTrace (prefixWord ++ tailWord_409021) baseStart_409021 baseEnd_409021 := by
    simpa [prefixWord, tailWord_409021, baseEnd_409021] using wordTrace_append hprefix tailTrace_409021
  have hstable : (prefixWord ++ tailWord_409021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409021).length < 2 ^ (prefixWord ++ tailWord_409021).sum := by decide
  have hdescent : baseEnd_409021 < baseStart_409021 := by decide
  rcases family_descends (prefixWord ++ tailWord_409021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409107 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 3]
def baseStart_409107 : Nat := 118140960795 + 409107 * 2 ^ 59
def prefixEnd_409107 : Nat := 4983230072969 + 3 ^ 40 * 409107 * 2
def baseEnd_409107 : Nat := 186727582328032089494273

theorem tailTrace_409107 : CollatzResearch.WordTrace tailWord_409107 prefixEnd_409107 186727582328032089494273 := by
  unfold tailWord_409107
  simp only [CollatzResearch.WordTrace]
  refine ⟨14921358128882683758081575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9947572085921789172054383 14921358128882683758081575)
  ·
    refine ⟨22382037193324025637122363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14921358128882683758081575 22382037193324025637122363)
    ·
      refine ⟨33573055789986038455683545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22382037193324025637122363 33573055789986038455683545)
      ·
        refine ⟨25179791842489528841762659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33573055789986038455683545 25179791842489528841762659)
        ·
          refine ⟨37769687763734293262643989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25179791842489528841762659 37769687763734293262643989)
          ·
            refine ⟨1770454113925044996686437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37769687763734293262643989 1770454113925044996686437)
            ·
              refine ⟨331960146360945936878707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1770454113925044996686437 331960146360945936878707)
              ·
                refine ⟨497940219541418905318061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331960146360945936878707 497940219541418905318061)
                ·
                  refine ⟨186727582328032089494273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497940219541418905318061 186727582328032089494273)
                  ·
                    rfl

theorem cell20_409107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_409107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409107 prefixEnd_409107 := by exact prefixLift 409107
  have htrace : WordTrace (prefixWord ++ tailWord_409107) baseStart_409107 baseEnd_409107 := by
    simpa [prefixWord, tailWord_409107, baseEnd_409107] using wordTrace_append hprefix tailTrace_409107
  have hstable : (prefixWord ++ tailWord_409107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409107).length < 2 ^ (prefixWord ++ tailWord_409107).sum := by decide
  have hdescent : baseEnd_409107 < baseStart_409107 := by decide
  rcases family_descends (prefixWord ++ tailWord_409107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409145 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_409145 : Nat := 118140960795 + 409145 * 2 ^ 59
def prefixEnd_409145 : Nat := 4983230072969 + 3 ^ 40 * 409145 * 2
def baseEnd_409145 : Nat := 186744926563472846227451

theorem tailTrace_409145 : CollatzResearch.WordTrace tailWord_409145 prefixEnd_409145 186744926563472846227451 := by
  unfold tailWord_409145
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922744102745016247964889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9948496068496677498643259 14922744102745016247964889)
  ·
    refine ⟨11192058077058762185973667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14922744102745016247964889 11192058077058762185973667)
    ·
      refine ⟨16788087115588143278960501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11192058077058762185973667 16788087115588143278960501)
      ·
        refine ⟨1573883167086388432402547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16788087115588143278960501 1573883167086388432402547)
        ·
          refine ⟨2360824750629582648603821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573883167086388432402547 2360824750629582648603821)
          ·
            refine ⟨885309281486093493226433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2360824750629582648603821 885309281486093493226433)
            ·
              refine ⟨663981961114570119919825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885309281486093493226433 663981961114570119919825)
              ·
                refine ⟨497986470835927589939869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663981961114570119919825 497986470835927589939869)
                ·
                  refine ⟨186744926563472846227451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497986470835927589939869 186744926563472846227451)
                  ·
                    rfl

theorem cell20_409145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_409145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409145 prefixEnd_409145 := by exact prefixLift 409145
  have htrace : WordTrace (prefixWord ++ tailWord_409145) baseStart_409145 baseEnd_409145 := by
    simpa [prefixWord, tailWord_409145, baseEnd_409145] using wordTrace_append hprefix tailTrace_409145
  have hstable : (prefixWord ++ tailWord_409145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409145).length < 2 ^ (prefixWord ++ tailWord_409145).sum := by decide
  have hdescent : baseEnd_409145 < baseStart_409145 := by decide
  rcases family_descends (prefixWord ++ tailWord_409145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409197 : List Nat := [1, 5, 1, 1, 4, 1, 7]
def baseStart_409197 : Nat := 118140960795 + 409197 * 2 ^ 59
def prefixEnd_409197 : Nat := 4983230072969 + 3 ^ 40 * 409197 * 2
def baseEnd_409197 : Nat := 20752073420043530721545

theorem tailTrace_409197 : CollatzResearch.WordTrace tailWord_409197 prefixEnd_409197 20752073420043530721545 := by
  unfold tailWord_409197
  simp only [CollatzResearch.WordTrace]
  refine ⟨14924640698556629128857845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9949760465704419419238563 14924640698556629128857845)
  ·
    refine ⟨1399185065489683980830423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14924640698556629128857845 1399185065489683980830423)
    ·
      refine ⟨2098777598234525971245635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399185065489683980830423 2098777598234525971245635)
      ·
        refine ⟨3148166397351788956868453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098777598234525971245635 3148166397351788956868453)
        ·
          refine ⟨590281199503460429412835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3148166397351788956868453 590281199503460429412835)
          ·
            refine ⟨885421799255190644119253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590281199503460429412835 885421799255190644119253)
            ·
              refine ⟨20752073420043530721545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 885421799255190644119253 20752073420043530721545)
              ·
                rfl

theorem cell20_409197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_409197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409197 prefixEnd_409197 := by exact prefixLift 409197
  have htrace : WordTrace (prefixWord ++ tailWord_409197) baseStart_409197 baseEnd_409197 := by
    simpa [prefixWord, tailWord_409197, baseEnd_409197] using wordTrace_append hprefix tailTrace_409197
  have hstable : (prefixWord ++ tailWord_409197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409197).length < 2 ^ (prefixWord ++ tailWord_409197).sum := by decide
  have hdescent : baseEnd_409197 < baseStart_409197 := by decide
  rcases family_descends (prefixWord ++ tailWord_409197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409211 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_409211 : Nat := 118140960795 + 409211 * 2 ^ 59
def prefixEnd_409211 : Nat := 4983230072969 + 3 ^ 40 * 409211 * 2
def baseEnd_409211 : Nat := 186775050761869950027181

theorem tailTrace_409211 : CollatzResearch.WordTrace tailWord_409211 prefixEnd_409211 186775050761869950027181 := by
  unfold tailWord_409211
  simp only [CollatzResearch.WordTrace]
  refine ⟨14925151320505909519867487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9950100880337273013244991 14925151320505909519867487)
  ·
    refine ⟨22387726980758864279801231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14925151320505909519867487 22387726980758864279801231)
    ·
      refine ⟨33581590471138296419701847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22387726980758864279801231 33581590471138296419701847)
      ·
        refine ⟨50372385706707444629552771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33581590471138296419701847 50372385706707444629552771)
        ·
          refine ⟨75558578560061166944329157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50372385706707444629552771 75558578560061166944329157)
          ·
            refine ⟨14167233480011468802061717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75558578560061166944329157 14167233480011468802061717)
            ·
              refine ⟨664089069375537600096643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14167233480011468802061717 664089069375537600096643)
              ·
                refine ⟨996133604063306400144965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664089069375537600096643 996133604063306400144965)
                ·
                  refine ⟨186775050761869950027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996133604063306400144965 186775050761869950027181)
                  ·
                    rfl

theorem cell20_409211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_409211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409211 prefixEnd_409211 := by exact prefixLift 409211
  have htrace : WordTrace (prefixWord ++ tailWord_409211) baseStart_409211 baseEnd_409211 := by
    simpa [prefixWord, tailWord_409211, baseEnd_409211] using wordTrace_append hprefix tailTrace_409211
  have hstable : (prefixWord ++ tailWord_409211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409211).length < 2 ^ (prefixWord ++ tailWord_409211).sum := by decide
  have hdescent : baseEnd_409211 < baseStart_409211 := by decide
  rcases family_descends (prefixWord ++ tailWord_409211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409221 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 3]
def baseStart_409221 : Nat := 118140960795 + 409221 * 2 ^ 59
def prefixEnd_409221 : Nat := 4983230072969 + 3 ^ 40 * 409221 * 2
def baseEnd_409221 : Nat := 186779615034354359693807

theorem tailTrace_409221 : CollatzResearch.WordTrace tailWord_409221 prefixEnd_409221 186779615034354359693807 := by
  unfold tailWord_409221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14925516050469681227731517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9950344033646454151821011 14925516050469681227731517)
  ·
    refine ⟨5597068518926130460399319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14925516050469681227731517 5597068518926130460399319)
    ·
      refine ⟨8395602778389195690598979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5597068518926130460399319 8395602778389195690598979)
      ·
        refine ⟨12593404167583793535898469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8395602778389195690598979 12593404167583793535898469)
        ·
          refine ⟨2361263281421961287980963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12593404167583793535898469 2361263281421961287980963)
          ·
            refine ⟨3541894922132941931971445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361263281421961287980963 3541894922132941931971445)
            ·
              refine ⟨332052648949963306122323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3541894922132941931971445 332052648949963306122323)
              ·
                refine ⟨498078973424944959183485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332052648949963306122323 498078973424944959183485)
                ·
                  refine ⟨186779615034354359693807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498078973424944959183485 186779615034354359693807)
                  ·
                    rfl

theorem cell20_409221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_409221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409221 prefixEnd_409221 := by exact prefixLift 409221
  have htrace : WordTrace (prefixWord ++ tailWord_409221) baseStart_409221 baseEnd_409221 := by
    simpa [prefixWord, tailWord_409221, baseEnd_409221] using wordTrace_append hprefix tailTrace_409221
  have hstable : (prefixWord ++ tailWord_409221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409221).length < 2 ^ (prefixWord ++ tailWord_409221).sum := by decide
  have hdescent : baseEnd_409221 < baseStart_409221 := by decide
  rcases family_descends (prefixWord ++ tailWord_409221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409262 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_409262 : Nat := 118140960795 + 409262 * 2 ^ 59
def prefixEnd_409262 : Nat := 4983230072969 + 3 ^ 40 * 409262 * 2
def baseEnd_409262 : Nat := 186798328551540439326973

theorem tailTrace_409262 : CollatzResearch.WordTrace tailWord_409262 prefixEnd_409262 186798328551540439326973 := by
  unfold tailWord_409262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865876430415143153746755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9951340962214096819982693 1865876430415143153746755)
  ·
    refine ⟨2798814645622714730620133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865876430415143153746755 2798814645622714730620133)
    ·
      refine ⟨524777746054259011991275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2798814645622714730620133 524777746054259011991275)
      ·
        refine ⟨787166619081388517986913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524777746054259011991275 787166619081388517986913)
        ·
          refine ⟨590374964311041388490185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787166619081388517986913 590374964311041388490185)
          ·
            refine ⟨442781223233281041367639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590374964311041388490185 442781223233281041367639)
            ·
              refine ⟨664171834849921562051459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442781223233281041367639 664171834849921562051459)
              ·
                refine ⟨996257752274882343077189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664171834849921562051459 996257752274882343077189)
                ·
                  refine ⟨186798328551540439326973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996257752274882343077189 186798328551540439326973)
                  ·
                    rfl

theorem cell20_409262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_409262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409262 prefixEnd_409262 := by exact prefixLift 409262
  have htrace : WordTrace (prefixWord ++ tailWord_409262) baseStart_409262 baseEnd_409262 := by
    simpa [prefixWord, tailWord_409262, baseEnd_409262] using wordTrace_append hprefix tailTrace_409262
  have hstable : (prefixWord ++ tailWord_409262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409262).length < 2 ^ (prefixWord ++ tailWord_409262).sum := by decide
  have hdescent : baseEnd_409262 < baseStart_409262 := by decide
  rcases family_descends (prefixWord ++ tailWord_409262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409263 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_409263 : Nat := 118140960795 + 409263 * 2 ^ 59
def prefixEnd_409263 : Nat := 4983230072969 + 3 ^ 40 * 409263 * 2
def baseEnd_409263 : Nat := 186798784978788880293635

theorem tailTrace_409263 : CollatzResearch.WordTrace tailWord_409263 prefixEnd_409263 186798784978788880293635 := by
  unfold tailWord_409263
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927047916317522400760443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9951365277545014933840295 14927047916317522400760443)
  ·
    refine ⟨22390571874476283601140665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14927047916317522400760443 22390571874476283601140665)
    ·
      refine ⟨16792928905857212700855499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22390571874476283601140665 16792928905857212700855499)
      ·
        refine ⟨25189393358785819051283249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16792928905857212700855499 25189393358785819051283249)
        ·
          refine ⟨18892045019089364288462437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25189393358785819051283249 18892045019089364288462437)
          ·
            refine ⟨3542258441079255804086707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18892045019089364288462437 3542258441079255804086707)
            ·
              refine ⟨5313387661618883706130061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542258441079255804086707 5313387661618883706130061)
              ·
                refine ⟨1992520373107081389798773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5313387661618883706130061 1992520373107081389798773)
                ·
                  refine ⟨186798784978788880293635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1992520373107081389798773 186798784978788880293635)
                  ·
                    rfl

theorem cell20_409263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_409263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409263 prefixEnd_409263 := by exact prefixLift 409263
  have htrace : WordTrace (prefixWord ++ tailWord_409263) baseStart_409263 baseEnd_409263 := by
    simpa [prefixWord, tailWord_409263, baseEnd_409263] using wordTrace_append hprefix tailTrace_409263
  have hstable : (prefixWord ++ tailWord_409263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409263).length < 2 ^ (prefixWord ++ tailWord_409263).sum := by decide
  have hdescent : baseEnd_409263 < baseStart_409263 := by decide
  rcases family_descends (prefixWord ++ tailWord_409263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409266 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_409266 : Nat := 118140960795 + 409266 * 2 ^ 59
def prefixEnd_409266 : Nat := 4983230072969 + 3 ^ 40 * 409266 * 2
def baseEnd_409266 : Nat := 186800154260534203193623

theorem tailTrace_409266 : CollatzResearch.WordTrace tailWord_409266 prefixEnd_409266 186800154260534203193623 := by
  unfold tailWord_409266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731789333826663478279913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9951438223537769275413101 3731789333826663478279913)
  ·
    refine ⟨2798842000369997608709935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3731789333826663478279913 2798842000369997608709935)
    ·
      refine ⟨4198263000554996413064903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798842000369997608709935 4198263000554996413064903)
      ·
        refine ⟨6297394500832494619597355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198263000554996413064903 6297394500832494619597355)
        ·
          refine ⟨9446091751248741929396033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297394500832494619597355 9446091751248741929396033)
          ·
            refine ⟨7084568813436556447047025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9446091751248741929396033 7084568813436556447047025)
            ·
              refine ⟨5313426610077417335285269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7084568813436556447047025 5313426610077417335285269)
              ·
                refine ⟨249066872347378937591497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5313426610077417335285269 249066872347378937591497)
                ·
                  refine ⟨186800154260534203193623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249066872347378937591497 186800154260534203193623)
                  ·
                    rfl

theorem cell20_409266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_409266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409266 prefixEnd_409266 := by exact prefixLift 409266
  have htrace : WordTrace (prefixWord ++ tailWord_409266) baseStart_409266 baseEnd_409266 := by
    simpa [prefixWord, tailWord_409266, baseEnd_409266] using wordTrace_append hprefix tailTrace_409266
  have hstable : (prefixWord ++ tailWord_409266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409266).length < 2 ^ (prefixWord ++ tailWord_409266).sum := by decide
  have hdescent : baseEnd_409266 < baseStart_409266 := by decide
  rcases family_descends (prefixWord ++ tailWord_409266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409276 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_409276 : Nat := 118140960795 + 409276 * 2 ^ 59
def prefixEnd_409276 : Nat := 4983230072969 + 3 ^ 40 * 409276 * 2
def baseEnd_409276 : Nat := 186804718533018612860249

theorem tailTrace_409276 : CollatzResearch.WordTrace tailWord_409276 prefixEnd_409276 186804718533018612860249 := by
  unfold tailWord_409276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463761032635212810491841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9951681376846950413989121 7463761032635212810491841)
  ·
    refine ⟨5597820774476409607868881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7463761032635212810491841 5597820774476409607868881)
    ·
      refine ⟨4198365580857307205901661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5597820774476409607868881 4198365580857307205901661)
      ·
        refine ⟨1574387092821490202213123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4198365580857307205901661 1574387092821490202213123)
        ·
          refine ⟨2361580639232235303319685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574387092821490202213123 2361580639232235303319685)
          ·
            refine ⟨442796369856044119372441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2361580639232235303319685 442796369856044119372441)
            ·
              refine ⟨332097277392033089529331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442796369856044119372441 332097277392033089529331)
              ·
                refine ⟨498145916088049634293997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332097277392033089529331 498145916088049634293997)
                ·
                  refine ⟨186804718533018612860249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498145916088049634293997 186804718533018612860249)
                  ·
                    rfl

theorem cell20_409276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_409276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409276 prefixEnd_409276 := by exact prefixLift 409276
  have htrace : WordTrace (prefixWord ++ tailWord_409276) baseStart_409276 baseEnd_409276 := by
    simpa [prefixWord, tailWord_409276, baseEnd_409276] using wordTrace_append hprefix tailTrace_409276
  have hstable : (prefixWord ++ tailWord_409276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409276).length < 2 ^ (prefixWord ++ tailWord_409276).sum := by decide
  have hdescent : baseEnd_409276 < baseStart_409276 := by decide
  rcases family_descends (prefixWord ++ tailWord_409276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409280 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_409280 : Nat := 118140960795 + 409280 * 2 ^ 59
def prefixEnd_409280 : Nat := 4983230072969 + 3 ^ 40 * 409280 * 2
def baseEnd_409280 : Nat := 186806544242012376726899

theorem tailTrace_409280 : CollatzResearch.WordTrace tailWord_409280 prefixEnd_409280 186806544242012376726899 := by
  unfold tailWord_409280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7463833978627967152064647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9951778638170622869419529 7463833978627967152064647)
  ·
    refine ⟨11195750967941950728096971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7463833978627967152064647 11195750967941950728096971)
    ·
      refine ⟨16793626451912926092145457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11195750967941950728096971 16793626451912926092145457)
      ·
        refine ⟨12595219838934694569109093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16793626451912926092145457 12595219838934694569109093)
        ·
          refine ⟨2361603719800255231707955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12595219838934694569109093 2361603719800255231707955)
          ·
            refine ⟨3542405579700382847561933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361603719800255231707955 3542405579700382847561933)
            ·
              refine ⟨1328402092387643567835725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3542405579700382847561933 1328402092387643567835725)
              ·
                refine ⟨498150784645366337938397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328402092387643567835725 498150784645366337938397)
                ·
                  refine ⟨186806544242012376726899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498150784645366337938397 186806544242012376726899)
                  ·
                    rfl

theorem cell20_409280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_409280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409280 prefixEnd_409280 := by exact prefixLift 409280
  have htrace : WordTrace (prefixWord ++ tailWord_409280) baseStart_409280 baseEnd_409280 := by
    simpa [prefixWord, tailWord_409280, baseEnd_409280] using wordTrace_append hprefix tailTrace_409280
  have hstable : (prefixWord ++ tailWord_409280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409280).length < 2 ^ (prefixWord ++ tailWord_409280).sum := by decide
  have hdescent : baseEnd_409280 < baseStart_409280 := by decide
  rcases family_descends (prefixWord ++ tailWord_409280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409294 : List Nat := [4, 1, 1, 1, 3, 1, 1, 8]
def baseStart_409294 : Nat := 118140960795 + 409294 * 2 ^ 59
def prefixEnd_409294 : Nat := 4983230072969 + 3 ^ 40 * 409294 * 2
def baseEnd_409294 : Nat := 62270978074496850086725

theorem tailTrace_409294 : CollatzResearch.WordTrace tailWord_409294 prefixEnd_409294 62270978074496850086725 := by
  unfold tailWord_409294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866022322400651836892367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9952119052803476463425957 1866022322400651836892367)
  ·
    refine ⟨2799033483600977755338551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866022322400651836892367 2799033483600977755338551)
    ·
      refine ⟨4198550225401466633007827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799033483600977755338551 4198550225401466633007827)
      ·
        refine ⟨6297825338102199949511741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198550225401466633007827 6297825338102199949511741)
        ·
          refine ⟨2361684501788324981066903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6297825338102199949511741 2361684501788324981066903)
          ·
            refine ⟨3542526752682487471600355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361684501788324981066903 3542526752682487471600355)
            ·
              refine ⟨5313790129023731207400533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542526752682487471600355 5313790129023731207400533)
              ·
                refine ⟨62270978074496850086725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5313790129023731207400533 62270978074496850086725)
                ·
                  rfl

theorem cell20_409294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_409294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409294 prefixEnd_409294 := by exact prefixLift 409294
  have htrace : WordTrace (prefixWord ++ tailWord_409294) baseStart_409294 baseEnd_409294 := by
    simpa [prefixWord, tailWord_409294, baseEnd_409294] using wordTrace_append hprefix tailTrace_409294
  have hstable : (prefixWord ++ tailWord_409294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409294).length < 2 ^ (prefixWord ++ tailWord_409294).sum := by decide
  have hdescent : baseEnd_409294 < baseStart_409294 := by decide
  rcases family_descends (prefixWord ++ tailWord_409294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409304 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 2]
def baseStart_409304 : Nat := 118140960795 + 409304 * 2 ^ 59
def prefixEnd_409304 : Nat := 4983230072969 + 3 ^ 40 * 409304 * 2
def baseEnd_409304 : Nat := 186817498495974959926801

theorem tailTrace_409304 : CollatzResearch.WordTrace tailWord_409304 prefixEnd_409304 186817498495974959926801 := by
  unfold tailWord_409304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464271654584493201501483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9952362206112657602001977 7464271654584493201501483)
  ·
    refine ⟨11196407481876739802252225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7464271654584493201501483 11196407481876739802252225)
    ·
      refine ⟨8397305611407554851689169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11196407481876739802252225 8397305611407554851689169)
      ·
        refine ⟨6297979208555666138766877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8397305611407554851689169 6297979208555666138766877)
        ·
          refine ⟨2361742203208374802037579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6297979208555666138766877 2361742203208374802037579)
          ·
            refine ⟨3542613304812562203056369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361742203208374802037579 3542613304812562203056369)
            ·
              refine ⟨2656959978609421652292277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3542613304812562203056369 2656959978609421652292277)
              ·
                refine ⟨249089997994633279902401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2656959978609421652292277 249089997994633279902401)
                ·
                  refine ⟨186817498495974959926801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249089997994633279902401 186817498495974959926801)
                  ·
                    rfl

theorem cell20_409304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_409304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409304 prefixEnd_409304 := by exact prefixLift 409304
  have htrace : WordTrace (prefixWord ++ tailWord_409304) baseStart_409304 baseEnd_409304 := by
    simpa [prefixWord, tailWord_409304, baseEnd_409304] using wordTrace_append hprefix tailTrace_409304
  have hstable : (prefixWord ++ tailWord_409304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409304).length < 2 ^ (prefixWord ++ tailWord_409304).sum := by decide
  have hdescent : baseEnd_409304 < baseStart_409304 := by decide
  rcases family_descends (prefixWord ++ tailWord_409304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409370 : List Nat := [3, 1, 1, 3, 2, 3, 7]
def baseStart_409370 : Nat := 118140960795 + 409370 * 2 ^ 59
def prefixEnd_409370 : Nat := 4983230072969 + 3 ^ 40 * 409370 * 2
def baseEnd_409370 : Nat := 20760846966041340414059

theorem tailTrace_409370 : CollatzResearch.WordTrace tailWord_409370 prefixEnd_409370 20760846966041340414059 := by
  unfold tailWord_409370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732737631732469918726391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9953967017953253116603709 3732737631732469918726391)
  ·
    refine ⟨5599106447598704878089587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3732737631732469918726391 5599106447598704878089587)
    ·
      refine ⟨8398659671398057317134381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599106447598704878089587 8398659671398057317134381)
      ·
        refine ⟨3149497376774271493925393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8398659671398057317134381 3149497376774271493925393)
        ·
          refine ⟨2362123032580703620444045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3149497376774271493925393 2362123032580703620444045)
          ·
            refine ⟨885796137217763857666517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2362123032580703620444045 885796137217763857666517)
            ·
              refine ⟨20760846966041340414059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 885796137217763857666517 20760846966041340414059)
              ·
                rfl

theorem cell20_409370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_409370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409370 prefixEnd_409370 := by exact prefixLift 409370
  have htrace : WordTrace (prefixWord ++ tailWord_409370) baseStart_409370 baseEnd_409370 := by
    simpa [prefixWord, tailWord_409370, baseEnd_409370] using wordTrace_append hprefix tailTrace_409370
  have hstable : (prefixWord ++ tailWord_409370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409370).length < 2 ^ (prefixWord ++ tailWord_409370).sum := by decide
  have hdescent : baseEnd_409370 < baseStart_409370 := by decide
  rcases family_descends (prefixWord ++ tailWord_409370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409380 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_409380 : Nat := 118140960795 + 409380 * 2 ^ 59
def prefixEnd_409380 : Nat := 4983230072969 + 3 ^ 40 * 409380 * 2
def baseEnd_409380 : Nat := 186852186966856473393157

theorem tailTrace_409380 : CollatzResearch.WordTrace tailWord_409380 prefixEnd_409380 186852186966856473393157 := by
  unfold tailWord_409380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465657628446825691384797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9954210171262434255179729 7465657628446825691384797)
  ·
    refine ⟨2799621610667559634269299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7465657628446825691384797 2799621610667559634269299)
    ·
      refine ⟨4199432416001339451403949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799621610667559634269299 4199432416001339451403949)
      ·
        refine ⟨1574787156000502294276481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4199432416001339451403949 1574787156000502294276481)
        ·
          refine ⟨1181090367000376720707361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1574787156000502294276481 1181090367000376720707361)
          ·
            refine ⟨885817775250282540530521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181090367000376720707361 885817775250282540530521)
            ·
              refine ⟨664363331437711905397891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885817775250282540530521 664363331437711905397891)
              ·
                refine ⟨996544997156567858096837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664363331437711905397891 996544997156567858096837)
                ·
                  refine ⟨186852186966856473393157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996544997156567858096837 186852186966856473393157)
                  ·
                    rfl

theorem cell20_409380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_409380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409380 prefixEnd_409380 := by exact prefixLift 409380
  have htrace : WordTrace (prefixWord ++ tailWord_409380) baseStart_409380 baseEnd_409380 := by
    simpa [prefixWord, tailWord_409380, baseEnd_409380] using wordTrace_append hprefix tailTrace_409380
  have hstable : (prefixWord ++ tailWord_409380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409380).length < 2 ^ (prefixWord ++ tailWord_409380).sum := by decide
  have hdescent : baseEnd_409380 < baseStart_409380 := by decide
  rcases family_descends (prefixWord ++ tailWord_409380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409415 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_409415 : Nat := 118140960795 + 409415 * 2 ^ 59
def prefixEnd_409415 : Nat := 4983230072969 + 3 ^ 40 * 409415 * 2
def baseEnd_409415 : Nat := 186868161920551907226347

theorem tailTrace_409415 : CollatzResearch.WordTrace tailWord_409415 prefixEnd_409415 186868161920551907226347 := by
  unfold tailWord_409415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932591811766852360293699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9955061207844568240195799 14932591811766852360293699)
  ·
    refine ⟨22398887717650278540440549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14932591811766852360293699 22398887717650278540440549)
    ·
      refine ⟨4199791447059427226332603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22398887717650278540440549 4199791447059427226332603)
      ·
        refine ⟨6299687170589140839498905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199791447059427226332603 6299687170589140839498905)
        ·
          refine ⟨4724765377941855629624179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6299687170589140839498905 4724765377941855629624179)
          ·
            refine ⟨7087148066912783444436269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724765377941855629624179 7087148066912783444436269)
            ·
              refine ⟨2657680525092293791663601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7087148066912783444436269 2657680525092293791663601)
              ·
                refine ⟨1993260393819220343747701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2657680525092293791663601 1993260393819220343747701)
                ·
                  refine ⟨186868161920551907226347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993260393819220343747701 186868161920551907226347)
                  ·
                    rfl

theorem cell20_409415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_409415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409415 prefixEnd_409415 := by exact prefixLift 409415
  have htrace : WordTrace (prefixWord ++ tailWord_409415) baseStart_409415 baseEnd_409415 := by
    simpa [prefixWord, tailWord_409415, baseEnd_409415] using wordTrace_append hprefix tailTrace_409415
  have hstable : (prefixWord ++ tailWord_409415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409415).length < 2 ^ (prefixWord ++ tailWord_409415).sum := by decide
  have hdescent : baseEnd_409415 < baseStart_409415 := by decide
  rcases family_descends (prefixWord ++ tailWord_409415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409439 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_409439 : Nat := 118140960795 + 409439 * 2 ^ 59
def prefixEnd_409439 : Nat := 4983230072969 + 3 ^ 40 * 409439 * 2
def baseEnd_409439 : Nat := 186879116174514490426249

theorem tailTrace_409439 : CollatzResearch.WordTrace tailWord_409439 prefixEnd_409439 186879116174514490426249 := by
  unfold tailWord_409439
  simp only [CollatzResearch.WordTrace]
  refine ⟨14933467163679904459167371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9955644775786602972778247 14933467163679904459167371)
  ·
    refine ⟨22400200745519856688751057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14933467163679904459167371 22400200745519856688751057)
    ·
      refine ⟨16800150559139892516563293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22400200745519856688751057 16800150559139892516563293)
      ·
        refine ⟨6300056459677459693711235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16800150559139892516563293 6300056459677459693711235)
        ·
          refine ⟨9450084689516189540566853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6300056459677459693711235 9450084689516189540566853)
          ·
            refine ⟨1771890879284285538856285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9450084689516189540566853 1771890879284285538856285)
            ·
              refine ⟨664459079731607077071107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1771890879284285538856285 664459079731607077071107)
              ·
                refine ⟨996688619597410615606661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664459079731607077071107 996688619597410615606661)
                ·
                  refine ⟨186879116174514490426249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 996688619597410615606661 186879116174514490426249)
                  ·
                    rfl

theorem cell20_409439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_409439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409439 prefixEnd_409439 := by exact prefixLift 409439
  have htrace : WordTrace (prefixWord ++ tailWord_409439) baseStart_409439 baseEnd_409439 := by
    simpa [prefixWord, tailWord_409439, baseEnd_409439] using wordTrace_append hprefix tailTrace_409439
  have hstable : (prefixWord ++ tailWord_409439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409439).length < 2 ^ (prefixWord ++ tailWord_409439).sum := by decide
  have hdescent : baseEnd_409439 < baseStart_409439 := by decide
  rcases family_descends (prefixWord ++ tailWord_409439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409486 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_409486 : Nat := 118140960795 + 409486 * 2 ^ 59
def prefixEnd_409486 : Nat := 4983230072969 + 3 ^ 40 * 409486 * 2
def baseEnd_409486 : Nat := 186900568255191215859391

theorem tailTrace_409486 : CollatzResearch.WordTrace tailWord_409486 prefixEnd_409486 186900568255191215859391 := by
  unfold tailWord_409486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1866897674313703935766039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9956787596339754324085541 1866897674313703935766039)
  ·
    refine ⟨2800346511470555903649059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1866897674313703935766039 2800346511470555903649059)
    ·
      refine ⟨4200519767205833855473589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800346511470555903649059 4200519767205833855473589)
      ·
        refine ⟨393798728175546923950649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4200519767205833855473589 393798728175546923950649)
        ·
          refine ⟨295349046131660192962987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393798728175546923950649 295349046131660192962987)
          ·
            refine ⟨443023569197490289444481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295349046131660192962987 443023569197490289444481)
            ·
              refine ⟨332267676898117717083361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443023569197490289444481 332267676898117717083361)
              ·
                refine ⟨249200757673588287812521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332267676898117717083361 249200757673588287812521)
                ·
                  refine ⟨186900568255191215859391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249200757673588287812521 186900568255191215859391)
                  ·
                    rfl

theorem cell20_409486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_409486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409486 prefixEnd_409486 := by exact prefixLift 409486
  have htrace : WordTrace (prefixWord ++ tailWord_409486) baseStart_409486 baseEnd_409486 := by
    simpa [prefixWord, tailWord_409486, baseEnd_409486] using wordTrace_append hprefix tailTrace_409486
  have hstable : (prefixWord ++ tailWord_409486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409486).length < 2 ^ (prefixWord ++ tailWord_409486).sum := by decide
  have hdescent : baseEnd_409486 < baseStart_409486 := by decide
  rcases family_descends (prefixWord ++ tailWord_409486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409490 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_409490 : Nat := 118140960795 + 409490 * 2 ^ 59
def prefixEnd_409490 : Nat := 4983230072969 + 3 ^ 40 * 409490 * 2
def baseEnd_409490 : Nat := 186902393964184979726041

theorem tailTrace_409490 : CollatzResearch.WordTrace tailWord_409490 prefixEnd_409490 186902393964184979726041 := by
  unfold tailWord_409490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733831821623785042318481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9956884857663426779515949 3733831821623785042318481)
  ·
    refine ⟨2800373866217838781738861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3733831821623785042318481 2800373866217838781738861)
    ·
      refine ⟨1050140199831689543152073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2800373866217838781738861 1050140199831689543152073)
      ·
        refine ⟨787605149873767157364055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050140199831689543152073 787605149873767157364055)
        ·
          refine ⟨1181407724810650736046083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787605149873767157364055 1181407724810650736046083)
          ·
            refine ⟨1772111587215976104069125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181407724810650736046083 1772111587215976104069125)
            ·
              refine ⟨332270922602995519512961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1772111587215976104069125 332270922602995519512961)
              ·
                refine ⟨249203191952246639634721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332270922602995519512961 249203191952246639634721)
                ·
                  refine ⟨186902393964184979726041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249203191952246639634721 186902393964184979726041)
                  ·
                    rfl

theorem cell20_409490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_409490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409490 prefixEnd_409490 := by exact prefixLift 409490
  have htrace : WordTrace (prefixWord ++ tailWord_409490) baseStart_409490 baseEnd_409490 := by
    simpa [prefixWord, tailWord_409490, baseEnd_409490] using wordTrace_append hprefix tailTrace_409490
  have hstable : (prefixWord ++ tailWord_409490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409490).length < 2 ^ (prefixWord ++ tailWord_409490).sum := by decide
  have hdescent : baseEnd_409490 < baseStart_409490 := by decide
  rcases family_descends (prefixWord ++ tailWord_409490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409501 : List Nat := [1, 4, 2, 1, 2, 4, 1, 5]
def baseStart_409501 : Nat := 118140960795 + 409501 * 2 ^ 59
def prefixEnd_409501 : Nat := 4983230072969 + 3 ^ 40 * 409501 * 2
def baseEnd_409501 : Nat := 62302471554639276786443

theorem tailTrace_409501 : CollatzResearch.WordTrace tailWord_409501 prefixEnd_409501 62302471554639276786443 := by
  unfold tailWord_409501
  simp only [CollatzResearch.WordTrace]
  refine ⟨14935728489455289047924357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9957152326303526031949571 14935728489455289047924357)
  ·
    refine ⟨2800449091772866696485817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14935728489455289047924357 2800449091772866696485817)
    ·
      refine ⟨2100336818829650022364363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2800449091772866696485817 2100336818829650022364363)
      ·
        refine ⟨3150505228244475033546545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100336818829650022364363 3150505228244475033546545)
        ·
          refine ⟨2362878921183356275159909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150505228244475033546545 2362878921183356275159909)
          ·
            refine ⟨443039797721879301592483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2362878921183356275159909 443039797721879301592483)
            ·
              refine ⟨664559696582818952388725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443039797721879301592483 664559696582818952388725)
              ·
                refine ⟨62302471554639276786443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 664559696582818952388725 62302471554639276786443)
                ·
                  rfl

theorem cell20_409501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_409501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409501 prefixEnd_409501 := by exact prefixLift 409501
  have htrace : WordTrace (prefixWord ++ tailWord_409501) baseStart_409501 baseEnd_409501 := by
    simpa [prefixWord, tailWord_409501, baseEnd_409501] using wordTrace_append hprefix tailTrace_409501
  have hstable : (prefixWord ++ tailWord_409501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409501).length < 2 ^ (prefixWord ++ tailWord_409501).sum := by decide
  have hdescent : baseEnd_409501 < baseStart_409501 := by decide
  rcases family_descends (prefixWord ++ tailWord_409501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409508 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_409508 : Nat := 118140960795 + 409508 * 2 ^ 59
def prefixEnd_409508 : Nat := 4983230072969 + 3 ^ 40 * 409508 * 2
def baseEnd_409508 : Nat := 186910609654656917125967

theorem tailTrace_409508 : CollatzResearch.WordTrace tailWord_409508 prefixEnd_409508 186910609654656917125967 := by
  unfold tailWord_409508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7467991900214964621714589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9957322533619952828952785 7467991900214964621714589)
  ·
    refine ⟨2800496962580611733142971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7467991900214964621714589 2800496962580611733142971)
    ·
      refine ⟨4200745443870917599714457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800496962580611733142971 4200745443870917599714457)
      ·
        refine ⟨3150559082903188199785843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4200745443870917599714457 3150559082903188199785843)
        ·
          refine ⟨4725838624354782299678765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150559082903188199785843 4725838624354782299678765)
          ·
            refine ⟨1772189484133043362379537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4725838624354782299678765 1772189484133043362379537)
            ·
              refine ⟨1329142113099782521784653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772189484133043362379537 1329142113099782521784653)
              ·
                refine ⟨498428292412418445669245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1329142113099782521784653 498428292412418445669245)
                ·
                  refine ⟨186910609654656917125967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498428292412418445669245 186910609654656917125967)
                  ·
                    rfl

theorem cell20_409508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_409508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409508 prefixEnd_409508 := by exact prefixLift 409508
  have htrace : WordTrace (prefixWord ++ tailWord_409508) baseStart_409508 baseEnd_409508 := by
    simpa [prefixWord, tailWord_409508, baseEnd_409508] using wordTrace_append hprefix tailTrace_409508
  have hstable : (prefixWord ++ tailWord_409508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409508).length < 2 ^ (prefixWord ++ tailWord_409508).sum := by decide
  have hdescent : baseEnd_409508 < baseStart_409508 := by decide
  rcases family_descends (prefixWord ++ tailWord_409508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409529 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_409529 : Nat := 118140960795 + 409529 * 2 ^ 59
def prefixEnd_409529 : Nat := 4983230072969 + 3 ^ 40 * 409529 * 2
def baseEnd_409529 : Nat := 186920194626874177425881

theorem tailTrace_409529 : CollatzResearch.WordTrace tailWord_409529 prefixEnd_409529 186920194626874177425881 := by
  unfold tailWord_409529
  simp only [CollatzResearch.WordTrace]
  refine ⟨14936749733353849829943641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9957833155569233219962427 14936749733353849829943641)
  ·
    refine ⟨11202562300015387372457731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14936749733353849829943641 11202562300015387372457731)
    ·
      refine ⟨16803843450023081058686597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11202562300015387372457731 16803843450023081058686597)
      ·
        refine ⟨3150720646879327698503737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16803843450023081058686597 3150720646879327698503737)
        ·
          refine ⟨2363040485159495773877803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150720646879327698503737 2363040485159495773877803)
          ·
            refine ⟨3544560727739243660816705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363040485159495773877803 3544560727739243660816705)
            ·
              refine ⟨2658420545804432745612529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544560727739243660816705 2658420545804432745612529)
              ·
                refine ⟨1993815409353324559209397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658420545804432745612529 1993815409353324559209397)
                ·
                  refine ⟨186920194626874177425881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993815409353324559209397 186920194626874177425881)
                  ·
                    rfl

theorem cell20_409529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_409529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409529 prefixEnd_409529 := by exact prefixLift 409529
  have htrace : WordTrace (prefixWord ++ tailWord_409529) baseStart_409529 baseEnd_409529 := by
    simpa [prefixWord, tailWord_409529, baseEnd_409529] using wordTrace_append hprefix tailTrace_409529
  have hstable : (prefixWord ++ tailWord_409529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409529).length < 2 ^ (prefixWord ++ tailWord_409529).sum := by decide
  have hdescent : baseEnd_409529 < baseStart_409529 := by decide
  rcases family_descends (prefixWord ++ tailWord_409529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409536 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_409536 : Nat := 118140960795 + 409536 * 2 ^ 59
def prefixEnd_409536 : Nat := 4983230072969 + 3 ^ 40 * 409536 * 2
def baseEnd_409536 : Nat := 186923389617613264192519

theorem tailTrace_409536 : CollatzResearch.WordTrace tailWord_409536 prefixEnd_409536 186923389617613264192519 := by
  unfold tailWord_409536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468502522164245012724231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9958003362885660016965641 7468502522164245012724231)
  ·
    refine ⟨11202753783246367519086347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468502522164245012724231 11202753783246367519086347)
    ·
      refine ⟨16804130674869551278629521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11202753783246367519086347 16804130674869551278629521)
      ·
        refine ⟨12603098006152163458972141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16804130674869551278629521 12603098006152163458972141)
        ·
          refine ⟨4726161752307061297114553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12603098006152163458972141 4726161752307061297114553)
          ·
            refine ⟨3544621314230295972835915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4726161752307061297114553 3544621314230295972835915)
            ·
              refine ⟨5316931971345443959253873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544621314230295972835915 5316931971345443959253873)
              ·
                refine ⟨3987698978509082969440405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316931971345443959253873 3987698978509082969440405)
                ·
                  refine ⟨186923389617613264192519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3987698978509082969440405 186923389617613264192519)
                  ·
                    rfl

theorem cell20_409536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_409536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409536 prefixEnd_409536 := by exact prefixLift 409536
  have htrace : WordTrace (prefixWord ++ tailWord_409536) baseStart_409536 baseEnd_409536 := by
    simpa [prefixWord, tailWord_409536, baseEnd_409536] using wordTrace_append hprefix tailTrace_409536
  have hstable : (prefixWord ++ tailWord_409536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409536).length < 2 ^ (prefixWord ++ tailWord_409536).sum := by decide
  have hdescent : baseEnd_409536 < baseStart_409536 := by decide
  rcases family_descends (prefixWord ++ tailWord_409536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409546 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_409546 : Nat := 118140960795 + 409546 * 2 ^ 59
def prefixEnd_409546 : Nat := 4983230072969 + 3 ^ 40 * 409546 * 2
def baseEnd_409546 : Nat := 186927953890097673859145

theorem tailTrace_409546 : CollatzResearch.WordTrace tailWord_409546 prefixEnd_409546 186927953890097673859145 := by
  unfold tailWord_409546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734342443573065433328123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9958246516194841155541661 3734342443573065433328123)
  ·
    refine ⟨5601513665359598149992185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734342443573065433328123 5601513665359598149992185)
    ·
      refine ⟨4201135249019698612494139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5601513665359598149992185 4201135249019698612494139)
      ·
        refine ⟨6301702873529547918741209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201135249019698612494139 6301702873529547918741209)
        ·
          refine ⟨4726277155147160939055907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6301702873529547918741209 4726277155147160939055907)
          ·
            refine ⟨7089415732720741408583861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4726277155147160939055907 7089415732720741408583861)
            ·
              refine ⟨664632724942569507054737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7089415732720741408583861 664632724942569507054737)
              ·
                refine ⟨498474543706927130291053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664632724942569507054737 498474543706927130291053)
                ·
                  refine ⟨186927953890097673859145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498474543706927130291053 186927953890097673859145)
                  ·
                    rfl

theorem cell20_409546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_409546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409546 prefixEnd_409546 := by exact prefixLift 409546
  have htrace : WordTrace (prefixWord ++ tailWord_409546) baseStart_409546 baseEnd_409546 := by
    simpa [prefixWord, tailWord_409546, baseEnd_409546] using wordTrace_append hprefix tailTrace_409546
  have hstable : (prefixWord ++ tailWord_409546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409546).length < 2 ^ (prefixWord ++ tailWord_409546).sum := by decide
  have hdescent : baseEnd_409546 < baseStart_409546 := by decide
  rcases family_descends (prefixWord ++ tailWord_409546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409604 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 4]
def baseStart_409604 : Nat := 118140960795 + 409604 * 2 ^ 59
def prefixEnd_409604 : Nat := 4983230072969 + 3 ^ 40 * 409604 * 2
def baseEnd_409604 : Nat := 186954426670507249925575

theorem tailTrace_409604 : CollatzResearch.WordTrace tailWord_409604 prefixEnd_409604 186954426670507249925575 := by
  unfold tailWord_409604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7469742604041068819461933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9959656805388091759282577 7469742604041068819461933)
  ·
    refine ⟨2801153476515400807298225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7469742604041068819461933 2801153476515400807298225)
    ·
      refine ⟨2100865107386550605473669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2801153476515400807298225 2100865107386550605473669)
      ·
        refine ⟨393912207634978238526313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2100865107386550605473669 393912207634978238526313)
        ·
          refine ⟨295434155726233678894735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393912207634978238526313 295434155726233678894735)
          ·
            refine ⟨443151233589350518342103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295434155726233678894735 443151233589350518342103)
            ·
              refine ⟨664726850384025777513155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443151233589350518342103 664726850384025777513155)
              ·
                refine ⟨997090275576038666269733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664726850384025777513155 997090275576038666269733)
                ·
                  refine ⟨186954426670507249925575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997090275576038666269733 186954426670507249925575)
                  ·
                    rfl

theorem cell20_409604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_409604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409604 prefixEnd_409604 := by exact prefixLift 409604
  have htrace : WordTrace (prefixWord ++ tailWord_409604) baseStart_409604 baseEnd_409604 := by
    simpa [prefixWord, tailWord_409604, baseEnd_409604] using wordTrace_append hprefix tailTrace_409604
  have hstable : (prefixWord ++ tailWord_409604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409604).length < 2 ^ (prefixWord ++ tailWord_409604).sum := by decide
  have hdescent : baseEnd_409604 < baseStart_409604 := by decide
  rcases family_descends (prefixWord ++ tailWord_409604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409605 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_409605 : Nat := 118140960795 + 409605 * 2 ^ 59
def prefixEnd_409605 : Nat := 4983230072969 + 3 ^ 40 * 409605 * 2
def baseEnd_409605 : Nat := 186954883097755690892237

theorem tailTrace_409605 : CollatzResearch.WordTrace tailWord_409605 prefixEnd_409605 186954883097755690892237 := by
  unfold tailWord_409605
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939521681078514809710269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9959681120719009873140179 14939521681078514809710269)
  ·
    refine ⟨5602320630404443053641351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14939521681078514809710269 5602320630404443053641351)
    ·
      refine ⟨8403480945606664580462027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5602320630404443053641351 8403480945606664580462027)
      ·
        refine ⟨12605221418409996870693041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403480945606664580462027 12605221418409996870693041)
        ·
          refine ⟨9453916063807497653019781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12605221418409996870693041 9453916063807497653019781)
          ·
            refine ⟨1772609261963905809941209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9453916063807497653019781 1772609261963905809941209)
            ·
              refine ⟨1329456946472929357455907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772609261963905809941209 1329456946472929357455907)
              ·
                refine ⟨1994185419709394036183861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329456946472929357455907 1994185419709394036183861)
                ·
                  refine ⟨186954883097755690892237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1994185419709394036183861 186954883097755690892237)
                  ·
                    rfl

theorem cell20_409605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_409605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409605 prefixEnd_409605 := by exact prefixLift 409605
  have htrace : WordTrace (prefixWord ++ tailWord_409605) baseStart_409605 baseEnd_409605 := by
    simpa [prefixWord, tailWord_409605, baseEnd_409605] using wordTrace_append hprefix tailTrace_409605
  have hstable : (prefixWord ++ tailWord_409605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409605).length < 2 ^ (prefixWord ++ tailWord_409605).sum := by decide
  have hdescent : baseEnd_409605 < baseStart_409605 := by decide
  rcases family_descends (prefixWord ++ tailWord_409605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409619 : List Nat := [1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_409619 : Nat := 118140960795 + 409619 * 2 ^ 59
def prefixEnd_409619 : Nat := 4983230072969 + 3 ^ 40 * 409619 * 2
def baseEnd_409619 : Nat := 62320424359744621475171

theorem tailTrace_409619 : CollatzResearch.WordTrace tailWord_409619 prefixEnd_409619 62320424359744621475171 := by
  unfold tailWord_409619
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940032303027795200719911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9960021535351863467146607 14940032303027795200719911)
  ·
    refine ⟨22410048454541692801079867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14940032303027795200719911 22410048454541692801079867)
    ·
      refine ⟨33615072681812539201619801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22410048454541692801079867 33615072681812539201619801)
      ·
        refine ⟨25211304511359404401214851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33615072681812539201619801 25211304511359404401214851)
        ·
          refine ⟨37816956767039106601822277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25211304511359404401214851 37816956767039106601822277)
          ·
            refine ⟨7090679393819832487841677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37816956767039106601822277 7090679393819832487841677)
            ·
              refine ⟨2659004772682437182940629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7090679393819832487841677 2659004772682437182940629)
              ·
                refine ⟨62320424359744621475171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2659004772682437182940629 62320424359744621475171)
                ·
                  rfl

theorem cell20_409619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_409619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409619 prefixEnd_409619 := by exact prefixLift 409619
  have htrace : WordTrace (prefixWord ++ tailWord_409619) baseStart_409619 baseEnd_409619 := by
    simpa [prefixWord, tailWord_409619, baseEnd_409619] using wordTrace_append hprefix tailTrace_409619
  have hstable : (prefixWord ++ tailWord_409619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409619).length < 2 ^ (prefixWord ++ tailWord_409619).sum := by decide
  have hdescent : baseEnd_409619 < baseStart_409619 := by decide
  rcases family_descends (prefixWord ++ tailWord_409619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409657 : List Nat := [1, 2, 1, 5, 11]
def baseStart_409657 : Nat := 118140960795 + 409657 * 2 ^ 59
def prefixEnd_409657 : Nat := 4983230072969 + 3 ^ 40 * 409657 * 2
def baseEnd_409657 : Nat := 2308377991539192853811

theorem tailTrace_409657 : CollatzResearch.WordTrace tailWord_409657 prefixEnd_409657 2308377991539192853811 := by
  unfold tailWord_409657
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941418276890127690603225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9960945517926751793735483 14941418276890127690603225)
  ·
    refine ⟨11206063707667595767952419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14941418276890127690603225 11206063707667595767952419)
    ·
      refine ⟨16809095561501393651928629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11206063707667595767952419 16809095561501393651928629)
      ·
        refine ⟨1575852708890755654868309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16809095561501393651928629 1575852708890755654868309)
        ·
          refine ⟨2308377991539192853811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1575852708890755654868309 2308377991539192853811)
          ·
            rfl

theorem cell20_409657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 11].length) (baseStart_409657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409657 prefixEnd_409657 := by exact prefixLift 409657
  have htrace : WordTrace (prefixWord ++ tailWord_409657) baseStart_409657 baseEnd_409657 := by
    simpa [prefixWord, tailWord_409657, baseEnd_409657] using wordTrace_append hprefix tailTrace_409657
  have hstable : (prefixWord ++ tailWord_409657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409657).length < 2 ^ (prefixWord ++ tailWord_409657).sum := by decide
  have hdescent : baseEnd_409657 < baseStart_409657 := by decide
  rcases family_descends (prefixWord ++ tailWord_409657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409660 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_409660 : Nat := 118140960795 + 409660 * 2 ^ 59
def prefixEnd_409660 : Nat := 4983230072969 + 3 ^ 40 * 409660 * 2
def baseEnd_409660 : Nat := 186979986596419944058679

theorem tailTrace_409660 : CollatzResearch.WordTrace tailWord_409660 prefixEnd_409660 186979986596419944058679 := by
  unfold tailWord_409660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470763847939629601481217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9961018463919506135308289 7470763847939629601481217)
  ·
    refine ⟨5603072885954722201110913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7470763847939629601481217 5603072885954722201110913)
    ·
      refine ⟨4202304664466041650833185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5603072885954722201110913 4202304664466041650833185)
      ·
        refine ⟨3151728498349531238124889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4202304664466041650833185 3151728498349531238124889)
        ·
          refine ⟨2363796373762148428593667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3151728498349531238124889 2363796373762148428593667)
          ·
            refine ⟨3545694560643222642890501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363796373762148428593667 3545694560643222642890501)
            ·
              refine ⟨664817730120604245541969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3545694560643222642890501 664817730120604245541969)
              ·
                refine ⟨498613297590453184156477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664817730120604245541969 498613297590453184156477)
                ·
                  refine ⟨186979986596419944058679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498613297590453184156477 186979986596419944058679)
                  ·
                    rfl

theorem cell20_409660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_409660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409660 prefixEnd_409660 := by exact prefixLift 409660
  have htrace : WordTrace (prefixWord ++ tailWord_409660) baseStart_409660 baseEnd_409660 := by
    simpa [prefixWord, tailWord_409660, baseEnd_409660] using wordTrace_append hprefix tailTrace_409660
  have hstable : (prefixWord ++ tailWord_409660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409660).length < 2 ^ (prefixWord ++ tailWord_409660).sum := by decide
  have hdescent : baseEnd_409660 < baseStart_409660 := by decide
  rcases family_descends (prefixWord ++ tailWord_409660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409688 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_409688 : Nat := 118140960795 + 409688 * 2 ^ 59
def prefixEnd_409688 : Nat := 4983230072969 + 3 ^ 40 * 409688 * 2
def baseEnd_409688 : Nat := 186992766559376291125231

theorem tailTrace_409688 : CollatzResearch.WordTrace tailWord_409688 prefixEnd_409688 186992766559376291125231 := by
  unfold tailWord_409688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7471274469888909992490859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9961699293185213323321145 7471274469888909992490859)
  ·
    refine ⟨11206911704833364988736289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7471274469888909992490859 11206911704833364988736289)
    ·
      refine ⟨8405183778625023741552217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11206911704833364988736289 8405183778625023741552217)
      ·
        refine ⟨6303887833968767806164163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8405183778625023741552217 6303887833968767806164163)
        ·
          refine ⟨9455831750953151709246245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6303887833968767806164163 9455831750953151709246245)
          ·
            refine ⟨1772968453303715945483671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9455831750953151709246245 1772968453303715945483671)
            ·
              refine ⟨2659452679955573918225507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772968453303715945483671 2659452679955573918225507)
              ·
                refine ⟨3989179019933360877338261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659452679955573918225507 3989179019933360877338261)
                ·
                  refine ⟨186992766559376291125231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3989179019933360877338261 186992766559376291125231)
                  ·
                    rfl

theorem cell20_409688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_409688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409688 prefixEnd_409688 := by exact prefixLift 409688
  have htrace : WordTrace (prefixWord ++ tailWord_409688) baseStart_409688 baseEnd_409688 := by
    simpa [prefixWord, tailWord_409688, baseEnd_409688] using wordTrace_append hprefix tailTrace_409688
  have hstable : (prefixWord ++ tailWord_409688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409688).length < 2 ^ (prefixWord ++ tailWord_409688).sum := by decide
  have hdescent : baseEnd_409688 < baseStart_409688 := by decide
  rcases family_descends (prefixWord ++ tailWord_409688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409719 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_409719 : Nat := 118140960795 + 409719 * 2 ^ 59
def prefixEnd_409719 : Nat := 4983230072969 + 3 ^ 40 * 409719 * 2
def baseEnd_409719 : Nat := 187006915804077961091771

theorem tailTrace_409719 : CollatzResearch.WordTrace tailWord_409719 prefixEnd_409719 187006915804077961091771 := by
  unfold tailWord_409719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14943679602665512279360211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9962453068443674852906807 14943679602665512279360211)
  ·
    refine ⟨22415519403998268419040317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14943679602665512279360211 22415519403998268419040317)
    ·
      refine ⟨8405819776499350657140119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22415519403998268419040317 8405819776499350657140119)
      ·
        refine ⟨12608729664749025985710179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405819776499350657140119 12608729664749025985710179)
        ·
          refine ⟨18913094497123538978565269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12608729664749025985710179 18913094497123538978565269)
          ·
            refine ⟨886551304552665889620247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18913094497123538978565269 886551304552665889620247)
            ·
              refine ⟨1329826956828998834430371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886551304552665889620247 1329826956828998834430371)
              ·
                refine ⟨1994740435243498251645557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329826956828998834430371 1994740435243498251645557)
                ·
                  refine ⟨187006915804077961091771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1994740435243498251645557 187006915804077961091771)
                  ·
                    rfl

theorem cell20_409719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_409719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409719 prefixEnd_409719 := by exact prefixLift 409719
  have htrace : WordTrace (prefixWord ++ tailWord_409719) baseStart_409719 baseEnd_409719 := by
    simpa [prefixWord, tailWord_409719, baseEnd_409719] using wordTrace_append hprefix tailTrace_409719
  have hstable : (prefixWord ++ tailWord_409719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409719).length < 2 ^ (prefixWord ++ tailWord_409719).sum := by decide
  have hdescent : baseEnd_409719 < baseStart_409719 := by decide
  rcases family_descends (prefixWord ++ tailWord_409719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409757 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_409757 : Nat := 118140960795 + 409757 * 2 ^ 59
def prefixEnd_409757 : Nat := 4983230072969 + 3 ^ 40 * 409757 * 2
def baseEnd_409757 : Nat := 187024260039518717824949

theorem tailTrace_409757 : CollatzResearch.WordTrace tailWord_409757 prefixEnd_409757 187024260039518717824949 := by
  unfold tailWord_409757
  simp only [CollatzResearch.WordTrace]
  refine ⟨14945065576527844769243525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9963377051018563179495683 14945065576527844769243525)
  ·
    refine ⟨2802199795598970894233161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14945065576527844769243525 2802199795598970894233161)
    ·
      refine ⟨2101649846699228170674871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2802199795598970894233161 2101649846699228170674871)
      ·
        refine ⟨3152474770048842256012307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101649846699228170674871 3152474770048842256012307)
        ·
          refine ⟨4728712155073263384018461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152474770048842256012307 4728712155073263384018461)
          ·
            refine ⟨1773267058152473769006923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4728712155073263384018461 1773267058152473769006923)
            ·
              refine ⟨2659900587228710653510385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773267058152473769006923 2659900587228710653510385)
              ·
                refine ⟨1994925440421532990132789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659900587228710653510385 1994925440421532990132789)
                ·
                  refine ⟨187024260039518717824949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1994925440421532990132789 187024260039518717824949)
                  ·
                    rfl

theorem cell20_409757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_409757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409757 prefixEnd_409757 := by exact prefixLift 409757
  have htrace : WordTrace (prefixWord ++ tailWord_409757) baseStart_409757 baseEnd_409757 := by
    simpa [prefixWord, tailWord_409757, baseEnd_409757] using wordTrace_append hprefix tailTrace_409757
  have hstable : (prefixWord ++ tailWord_409757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409757).length < 2 ^ (prefixWord ++ tailWord_409757).sum := by decide
  have hdescent : baseEnd_409757 < baseStart_409757 := by decide
  rcases family_descends (prefixWord ++ tailWord_409757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409760 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 2]
def baseStart_409760 : Nat := 118140960795 + 409760 * 2 ^ 59
def prefixEnd_409760 : Nat := 4983230072969 + 3 ^ 40 * 409760 * 2
def baseEnd_409760 : Nat := 187025629321264040724937

theorem tailTrace_409760 : CollatzResearch.WordTrace tailWord_409760 prefixEnd_409760 187025629321264040724937 := by
  unfold tailWord_409760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7472587497758488140801367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9963449997011317521068489 7472587497758488140801367)
  ·
    refine ⟨11208881246637732211202051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7472587497758488140801367 11208881246637732211202051)
    ·
      refine ⟨16813321869956598316803077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11208881246637732211202051 16813321869956598316803077)
      ·
        refine ⟨3152497850616862184400577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16813321869956598316803077 3152497850616862184400577)
        ·
          refine ⟨2364373387962646638300433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152497850616862184400577 2364373387962646638300433)
          ·
            refine ⟨1773280040971984978725325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2364373387962646638300433 1773280040971984978725325)
            ·
              refine ⟨664980015364494367021997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1773280040971984978725325 664980015364494367021997)
              ·
                refine ⟨249367505761685387633249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664980015364494367021997 249367505761685387633249)
                ·
                  refine ⟨187025629321264040724937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249367505761685387633249 187025629321264040724937)
                  ·
                    rfl

theorem cell20_409760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_409760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409760 prefixEnd_409760 := by exact prefixLift 409760
  have htrace : WordTrace (prefixWord ++ tailWord_409760) baseStart_409760 baseEnd_409760 := by
    simpa [prefixWord, tailWord_409760, baseEnd_409760] using wordTrace_append hprefix tailTrace_409760
  have hstable : (prefixWord ++ tailWord_409760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409760).length < 2 ^ (prefixWord ++ tailWord_409760).sum := by decide
  have hdescent : baseEnd_409760 < baseStart_409760 := by decide
  rcases family_descends (prefixWord ++ tailWord_409760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409767 : List Nat := [1, 1, 6, 2, 2, 2, 6]
def baseStart_409767 : Nat := 118140960795 + 409767 * 2 ^ 59
def prefixEnd_409767 : Nat := 4983230072969 + 3 ^ 40 * 409767 * 2
def baseEnd_409767 : Nat := 20780980479111458610175

theorem tailTrace_409767 : CollatzResearch.WordTrace tailWord_409767 prefixEnd_409767 20780980479111458610175 := by
  unfold tailWord_409767
  simp only [CollatzResearch.WordTrace]
  refine ⟨14945430306491616477107555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9963620204327744318071703 14945430306491616477107555)
  ·
    refine ⟨22418145459737424715661333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14945430306491616477107555 22418145459737424715661333)
    ·
      refine ⟨1050850568425191783546625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22418145459737424715661333 1050850568425191783546625)
      ·
        refine ⟨788137926318893837659969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050850568425191783546625 788137926318893837659969)
        ·
          refine ⟨591103444739170378244977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788137926318893837659969 591103444739170378244977)
          ·
            refine ⟨443327583554377783683733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591103444739170378244977 443327583554377783683733)
            ·
              refine ⟨20780980479111458610175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 443327583554377783683733 20780980479111458610175)
              ·
                rfl

theorem cell20_409767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_409767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409767 prefixEnd_409767 := by exact prefixLift 409767
  have htrace : WordTrace (prefixWord ++ tailWord_409767) baseStart_409767 baseEnd_409767 := by
    simpa [prefixWord, tailWord_409767, baseEnd_409767] using wordTrace_append hprefix tailTrace_409767
  have hstable : (prefixWord ++ tailWord_409767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409767).length < 2 ^ (prefixWord ++ tailWord_409767).sum := by decide
  have hdescent : baseEnd_409767 < baseStart_409767 := by decide
  rcases family_descends (prefixWord ++ tailWord_409767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409777 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 4]
def baseStart_409777 : Nat := 118140960795 + 409777 * 2 ^ 59
def prefixEnd_409777 : Nat := 4983230072969 + 3 ^ 40 * 409777 * 2
def baseEnd_409777 : Nat := 187033388584487537158201

theorem tailTrace_409777 : CollatzResearch.WordTrace tailWord_409777 prefixEnd_409777 187033388584487537158201 := by
  unfold tailWord_409777
  simp only [CollatzResearch.WordTrace]
  refine ⟨14945795036455388184971585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9963863357636925456647723 14945795036455388184971585)
  ·
    refine ⟨11209346277341541138728689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14945795036455388184971585 11209346277341541138728689)
    ·
      refine ⟨8407009708006155854046517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11209346277341541138728689 8407009708006155854046517)
      ·
        refine ⟨788157160125577111316861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8407009708006155854046517 788157160125577111316861)
        ·
          refine ⟨295558935047091416743823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 788157160125577111316861 295558935047091416743823)
          ·
            refine ⟨443338402570637125115735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295558935047091416743823 443338402570637125115735)
            ·
              refine ⟨665007603855955687673603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443338402570637125115735 665007603855955687673603)
              ·
                refine ⟨997511405783933531510405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665007603855955687673603 997511405783933531510405)
                ·
                  refine ⟨187033388584487537158201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997511405783933531510405 187033388584487537158201)
                  ·
                    rfl

theorem cell20_409777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_409777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409777 prefixEnd_409777 := by exact prefixLift 409777
  have htrace : WordTrace (prefixWord ++ tailWord_409777) baseStart_409777 baseEnd_409777 := by
    simpa [prefixWord, tailWord_409777, baseEnd_409777] using wordTrace_append hprefix tailTrace_409777
  have hstable : (prefixWord ++ tailWord_409777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409777).length < 2 ^ (prefixWord ++ tailWord_409777).sum := by decide
  have hdescent : baseEnd_409777 < baseStart_409777 := by decide
  rcases family_descends (prefixWord ++ tailWord_409777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409802 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_409802 : Nat := 118140960795 + 409802 * 2 ^ 59
def prefixEnd_409802 : Nat := 4983230072969 + 3 ^ 40 * 409802 * 2
def baseEnd_409802 : Nat := 187044799265698561324765

theorem tailTrace_409802 : CollatzResearch.WordTrace tailWord_409802 prefixEnd_409802 187044799265698561324765 := by
  unfold tailWord_409802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736676715341204363657915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9964471240909878303087773 3736676715341204363657915)
  ·
    refine ⟨5605015073011806545486873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3736676715341204363657915 5605015073011806545486873)
    ·
      refine ⟨4203761304758854909115155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5605015073011806545486873 4203761304758854909115155)
      ·
        refine ⟨6305641957138282363672733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203761304758854909115155 6305641957138282363672733)
        ·
          refine ⟨2364615733926855886377275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6305641957138282363672733 2364615733926855886377275)
          ·
            refine ⟨3546923600890283829565913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364615733926855886377275 3546923600890283829565913)
            ·
              refine ⟨2660192700667712872174435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3546923600890283829565913 2660192700667712872174435)
              ·
                refine ⟨3990289051001569308261653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660192700667712872174435 3990289051001569308261653)
                ·
                  refine ⟨187044799265698561324765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3990289051001569308261653 187044799265698561324765)
                  ·
                    rfl

theorem cell20_409802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_409802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409802 prefixEnd_409802 := by exact prefixLift 409802
  have htrace : WordTrace (prefixWord ++ tailWord_409802) baseStart_409802 baseEnd_409802 := by
    simpa [prefixWord, tailWord_409802, baseEnd_409802] using wordTrace_append hprefix tailTrace_409802
  have hstable : (prefixWord ++ tailWord_409802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409802).length < 2 ^ (prefixWord ++ tailWord_409802).sum := by decide
  have hdescent : baseEnd_409802 < baseStart_409802 := by decide
  rcases family_descends (prefixWord ++ tailWord_409802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409809 : List Nat := [1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_409809 : Nat := 118140960795 + 409809 * 2 ^ 59
def prefixEnd_409809 : Nat := 4983230072969 + 3 ^ 40 * 409809 * 2
def baseEnd_409809 : Nat := 62349331418812549363801

theorem tailTrace_409809 : CollatzResearch.WordTrace tailWord_409809 prefixEnd_409809 62349331418812549363801 := by
  unfold tailWord_409809
  simp only [CollatzResearch.WordTrace]
  refine ⟨14946962172339457650136481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9964641448226305100090987 14946962172339457650136481)
  ·
    refine ⟨11210221629254593237602361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14946962172339457650136481 11210221629254593237602361)
    ·
      refine ⟨8407666221940944928201771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11210221629254593237602361 8407666221940944928201771)
      ·
        refine ⟨12611499332911417392302657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8407666221940944928201771 12611499332911417392302657)
        ·
          refine ⟨9458624499683563044226993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12611499332911417392302657 9458624499683563044226993)
          ·
            refine ⟨7093968374762672283170245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9458624499683563044226993 7093968374762672283170245)
            ·
              refine ⟨1330119070268001053094421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7093968374762672283170245 1330119070268001053094421)
              ·
                refine ⟨62349331418812549363801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1330119070268001053094421 62349331418812549363801)
                ·
                  rfl

theorem cell20_409809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_409809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409809 prefixEnd_409809 := by exact prefixLift 409809
  have htrace : WordTrace (prefixWord ++ tailWord_409809) baseStart_409809 baseEnd_409809 := by
    simpa [prefixWord, tailWord_409809, baseEnd_409809] using wordTrace_append hprefix tailTrace_409809
  have hstable : (prefixWord ++ tailWord_409809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409809).length < 2 ^ (prefixWord ++ tailWord_409809).sum := by decide
  have hdescent : baseEnd_409809 < baseStart_409809 := by decide
  rcases family_descends (prefixWord ++ tailWord_409809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409888 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_409888 : Nat := 118140960795 + 409888 * 2 ^ 59
def prefixEnd_409888 : Nat := 4983230072969 + 3 ^ 40 * 409888 * 2
def baseEnd_409888 : Nat := 187084052009064484457747

theorem tailTrace_409888 : CollatzResearch.WordTrace tailWord_409888 prefixEnd_409888 187084052009064484457747 := by
  unfold tailWord_409888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7474921769526627071131159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9966562359368836094841545 7474921769526627071131159)
  ·
    refine ⟨11212382654289940606696739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7474921769526627071131159 11212382654289940606696739)
    ·
      refine ⟨16818573981434910910045109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11212382654289940606696739 16818573981434910910045109)
      ·
        refine ⟨1576741310759522897816729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16818573981434910910045109 1576741310759522897816729)
        ·
          refine ⟨1182555983069642173362547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1576741310759522897816729 1182555983069642173362547)
          ·
            refine ⟨1773833974604463260043821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182555983069642173362547 1773833974604463260043821)
            ·
              refine ⟨665187740476673722516433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1773833974604463260043821 665187740476673722516433)
              ·
                refine ⟨498890805357505291887325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665187740476673722516433 498890805357505291887325)
                ·
                  refine ⟨187084052009064484457747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498890805357505291887325 187084052009064484457747)
                  ·
                    rfl

theorem cell20_409888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_409888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409888 prefixEnd_409888 := by exact prefixLift 409888
  have htrace : WordTrace (prefixWord ++ tailWord_409888) baseStart_409888 baseEnd_409888 := by
    simpa [prefixWord, tailWord_409888, baseEnd_409888] using wordTrace_append hprefix tailTrace_409888
  have hstable : (prefixWord ++ tailWord_409888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409888).length < 2 ^ (prefixWord ++ tailWord_409888).sum := by decide
  have hdescent : baseEnd_409888 < baseStart_409888 := by decide
  rcases family_descends (prefixWord ++ tailWord_409888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409905 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 3]
def baseStart_409905 : Nat := 118140960795 + 409905 * 2 ^ 59
def prefixEnd_409905 : Nat := 4983230072969 + 3 ^ 40 * 409905 * 2
def baseEnd_409905 : Nat := 187091811272287980891011

theorem tailTrace_409905 : CollatzResearch.WordTrace tailWord_409905 prefixEnd_409905 187091811272287980891011 := by
  unfold tailWord_409905
  simp only [CollatzResearch.WordTrace]
  refine ⟨14950463579991666045631169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9966975719994444030420779 14950463579991666045631169)
  ·
    refine ⟨11212847684993749534223377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14950463579991666045631169 11212847684993749534223377)
    ·
      refine ⟨8409635763745312150667533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11212847684993749534223377 8409635763745312150667533)
      ·
        refine ⟨3153613411404492056500325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8409635763745312150667533 3153613411404492056500325)
        ·
          refine ⟨591302514638342260593811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3153613411404492056500325 591302514638342260593811)
          ·
            refine ⟨886953771957513390890717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591302514638342260593811 886953771957513390890717)
            ·
              refine ⟨332607664484067521584019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 886953771957513390890717 332607664484067521584019)
              ·
                refine ⟨498911496726101282376029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332607664484067521584019 498911496726101282376029)
                ·
                  refine ⟨187091811272287980891011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498911496726101282376029 187091811272287980891011)
                  ·
                    rfl

theorem cell20_409905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_409905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409905 prefixEnd_409905 := by exact prefixLift 409905
  have htrace : WordTrace (prefixWord ++ tailWord_409905) baseStart_409905 baseEnd_409905 := by
    simpa [prefixWord, tailWord_409905, baseEnd_409905] using wordTrace_append hprefix tailTrace_409905
  have hstable : (prefixWord ++ tailWord_409905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409905).length < 2 ^ (prefixWord ++ tailWord_409905).sum := by decide
  have hdescent : baseEnd_409905 < baseStart_409905 := by decide
  rcases family_descends (prefixWord ++ tailWord_409905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409916 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_409916 : Nat := 118140960795 + 409916 * 2 ^ 59
def prefixEnd_409916 : Nat := 4983230072969 + 3 ^ 40 * 409916 * 2
def baseEnd_409916 : Nat := 187096831972020831524299

theorem tailTrace_409916 : CollatzResearch.WordTrace tailWord_409916 prefixEnd_409916 187096831972020831524299 := by
  unfold tailWord_409916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7475432391475907462140801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9967243188634543282854401 7475432391475907462140801)
  ·
    refine ⟨5606574293606930596605601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7475432391475907462140801 5606574293606930596605601)
    ·
      refine ⟨4204930720205197947454201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5606574293606930596605601 4204930720205197947454201)
      ·
        refine ⟨3153698040153898460590651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4204930720205197947454201 3153698040153898460590651)
        ·
          refine ⟨4730547060230847690885977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153698040153898460590651 4730547060230847690885977)
          ·
            refine ⟨3547910295173135768164483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4730547060230847690885977 3547910295173135768164483)
            ·
              refine ⟨5321865442759703652246725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3547910295173135768164483 5321865442759703652246725)
              ·
                refine ⟨997849770517444434796261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5321865442759703652246725 997849770517444434796261)
                ·
                  refine ⟨187096831972020831524299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 997849770517444434796261 187096831972020831524299)
                  ·
                    rfl

theorem cell20_409916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_409916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409916 prefixEnd_409916 := by exact prefixLift 409916
  have htrace : WordTrace (prefixWord ++ tailWord_409916) baseStart_409916 baseEnd_409916 := by
    simpa [prefixWord, tailWord_409916, baseEnd_409916] using wordTrace_append hprefix tailTrace_409916
  have hstable : (prefixWord ++ tailWord_409916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409916).length < 2 ^ (prefixWord ++ tailWord_409916).sum := by decide
  have hdescent : baseEnd_409916 < baseStart_409916 := by decide
  rcases family_descends (prefixWord ++ tailWord_409916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409940 : List Nat := [2, 4, 1, 1, 2, 4, 6]
def baseStart_409940 : Nat := 118140960795 + 409940 * 2 ^ 59
def prefixEnd_409940 : Nat := 4983230072969 + 3 ^ 40 * 409940 * 2
def baseEnd_409940 : Nat := 20789754025109268302689

theorem tailTrace_409940 : CollatzResearch.WordTrace tailWord_409940 prefixEnd_409940 20789754025109268302689 := by
  unfold tailWord_409940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7475870067432433511577637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9967826756576578015436849 7475870067432433511577637)
  ·
    refine ⟨1401725637643581283420807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7475870067432433511577637 1401725637643581283420807)
    ·
      refine ⟨2102588456465371925131211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401725637643581283420807 2102588456465371925131211)
      ·
        refine ⟨3153882684698057887696817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102588456465371925131211 3153882684698057887696817)
        ·
          refine ⟨2365412013523543415772613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3153882684698057887696817 2365412013523543415772613)
          ·
            refine ⟨443514752535664390457365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2365412013523543415772613 443514752535664390457365)
            ·
              refine ⟨20789754025109268302689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 443514752535664390457365 20789754025109268302689)
              ·
                rfl

theorem cell20_409940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 6].length) (baseStart_409940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409940 prefixEnd_409940 := by exact prefixLift 409940
  have htrace : WordTrace (prefixWord ++ tailWord_409940) baseStart_409940 baseEnd_409940 := by
    simpa [prefixWord, tailWord_409940, baseEnd_409940] using wordTrace_append hprefix tailTrace_409940
  have hstable : (prefixWord ++ tailWord_409940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409940).length < 2 ^ (prefixWord ++ tailWord_409940).sum := by decide
  have hdescent : baseEnd_409940 < baseStart_409940 := by decide
  rcases family_descends (prefixWord ++ tailWord_409940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409961 : List Nat := [1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_409961 : Nat := 118140960795 + 409961 * 2 ^ 59
def prefixEnd_409961 : Nat := 4983230072969 + 3 ^ 40 * 409961 * 2
def baseEnd_409961 : Nat := 62372457066066891674705

theorem tailTrace_409961 : CollatzResearch.WordTrace tailWord_409961 prefixEnd_409961 62372457066066891674705 := by
  unfold tailWord_409961
  simp only [CollatzResearch.WordTrace]
  refine ⟨14952506067788787609669737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9968337378525858406446491 14952506067788787609669737)
  ·
    refine ⟨11214379550841590707252303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14952506067788787609669737 11214379550841590707252303)
    ·
      refine ⟨16821569326262386060878455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11214379550841590707252303 16821569326262386060878455)
      ·
        refine ⟨25232353989393579091317683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16821569326262386060878455 25232353989393579091317683)
        ·
          refine ⟨37848530984090368636976525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25232353989393579091317683 37848530984090368636976525)
          ·
            refine ⟨14193199119033888238866197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37848530984090368636976525 14193199119033888238866197)
            ·
              refine ⟨665306208704713511196853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14193199119033888238866197 665306208704713511196853)
              ·
                refine ⟨62372457066066891674705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665306208704713511196853 62372457066066891674705)
                ·
                  rfl

theorem cell20_409961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_409961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409961 prefixEnd_409961 := by exact prefixLift 409961
  have htrace : WordTrace (prefixWord ++ tailWord_409961) baseStart_409961 baseEnd_409961 := by
    simpa [prefixWord, tailWord_409961, baseEnd_409961] using wordTrace_append hprefix tailTrace_409961
  have hstable : (prefixWord ++ tailWord_409961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409961).length < 2 ^ (prefixWord ++ tailWord_409961).sum := by decide
  have hdescent : baseEnd_409961 < baseStart_409961 := by decide
  rcases family_descends (prefixWord ++ tailWord_409961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409964 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_409964 : Nat := 118140960795 + 409964 * 2 ^ 59
def prefixEnd_409964 : Nat := 4983230072969 + 3 ^ 40 * 409964 * 2
def baseEnd_409964 : Nat := 187118740479945997924103

theorem tailTrace_409964 : CollatzResearch.WordTrace tailWord_409964 prefixEnd_409964 187118740479945997924103 := by
  unfold tailWord_409964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476307743388959561014473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9968410324518612748019297 7476307743388959561014473)
  ·
    refine ⟨5607230807541719670760855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7476307743388959561014473 5607230807541719670760855)
    ·
      refine ⟨8410846211312579506141283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607230807541719670760855 8410846211312579506141283)
      ·
        refine ⟨12616269316968869259211925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8410846211312579506141283 12616269316968869259211925)
        ·
          refine ⟨591387624232915746525559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12616269316968869259211925 591387624232915746525559)
          ·
            refine ⟨887081436349373619788339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591387624232915746525559 887081436349373619788339)
            ·
              refine ⟨1330622154524060429682509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887081436349373619788339 1330622154524060429682509)
              ·
                refine ⟨498983307946522661130941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1330622154524060429682509 498983307946522661130941)
                ·
                  refine ⟨187118740479945997924103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498983307946522661130941 187118740479945997924103)
                  ·
                    rfl

theorem cell20_409964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_409964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_409964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_409964 prefixEnd_409964 := by exact prefixLift 409964
  have htrace : WordTrace (prefixWord ++ tailWord_409964) baseStart_409964 baseEnd_409964 := by
    simpa [prefixWord, tailWord_409964, baseEnd_409964] using wordTrace_append hprefix tailTrace_409964
  have hstable : (prefixWord ++ tailWord_409964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409964).length < 2 ^ (prefixWord ++ tailWord_409964).sum := by decide
  have hdescent : baseEnd_409964 < baseStart_409964 := by decide
  rcases family_descends (prefixWord ++ tailWord_409964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410009 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 2]
def baseStart_410009 : Nat := 118140960795 + 410009 * 2 ^ 59
def prefixEnd_410009 : Nat := 4983230072969 + 3 ^ 40 * 410009 * 2
def baseEnd_410009 : Nat := 187139279706125841423919

theorem tailTrace_410009 : CollatzResearch.WordTrace tailWord_410009 prefixEnd_410009 187139279706125841423919 := by
  unfold tailWord_410009
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954256771614891807417081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9969504514409927871611387 14954256771614891807417081)
  ·
    refine ⟨11215692578711168855562811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14954256771614891807417081 11215692578711168855562811)
    ·
      refine ⟨16823538868066753283344217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215692578711168855562811 16823538868066753283344217)
      ·
        refine ⟨12617654151050064962508163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16823538868066753283344217 12617654151050064962508163)
        ·
          refine ⟨18926481226575097443762245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12617654151050064962508163 18926481226575097443762245)
          ·
            refine ⟨3548715229982830770705421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18926481226575097443762245 3548715229982830770705421)
            ·
              refine ⟨1330768211243561539014533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3548715229982830770705421 1330768211243561539014533)
              ·
                refine ⟨249519039608167788565225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1330768211243561539014533 249519039608167788565225)
                ·
                  refine ⟨187139279706125841423919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249519039608167788565225 187139279706125841423919)
                  ·
                    rfl

theorem cell20_410009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_410009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410009 prefixEnd_410009 := by exact prefixLift 410009
  have htrace : WordTrace (prefixWord ++ tailWord_410009) baseStart_410009 baseEnd_410009 := by
    simpa [prefixWord, tailWord_410009, baseEnd_410009] using wordTrace_append hprefix tailTrace_410009
  have hstable : (prefixWord ++ tailWord_410009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410009).length < 2 ^ (prefixWord ++ tailWord_410009).sum := by decide
  have hdescent : baseEnd_410009 < baseStart_410009 := by decide
  rcases family_descends (prefixWord ++ tailWord_410009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410016 : List Nat := [2, 1, 1, 4, 1, 5, 1, 5]
def baseStart_410016 : Nat := 118140960795 + 410016 * 2 ^ 59
def prefixEnd_410016 : Nat := 4983230072969 + 3 ^ 40 * 410016 * 2
def baseEnd_410016 : Nat := 62380824898954976063519

theorem tailTrace_410016 : CollatzResearch.WordTrace tailWord_410016 prefixEnd_410016 62380824898954976063519 := by
  unfold tailWord_410016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477256041294766001460951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9969674721726354668614601 7477256041294766001460951)
  ·
    refine ⟨11215884061942149002191427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7477256041294766001460951 11215884061942149002191427)
    ·
      refine ⟨16823826092913223503287141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215884061942149002191427 16823826092913223503287141)
      ·
        refine ⟨3154467392421229406866339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16823826092913223503287141 3154467392421229406866339)
        ·
          refine ⟨4731701088631844110299509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154467392421229406866339 4731701088631844110299509)
          ·
            refine ⟨443596977059235385340579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4731701088631844110299509 443596977059235385340579)
            ·
              refine ⟨665395465588853078010869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443596977059235385340579 665395465588853078010869)
              ·
                refine ⟨62380824898954976063519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665395465588853078010869 62380824898954976063519)
                ·
                  rfl

theorem cell20_410016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_410016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410016 prefixEnd_410016 := by exact prefixLift 410016
  have htrace : WordTrace (prefixWord ++ tailWord_410016) baseStart_410016 baseEnd_410016 := by
    simpa [prefixWord, tailWord_410016, baseEnd_410016] using wordTrace_append hprefix tailTrace_410016
  have hstable : (prefixWord ++ tailWord_410016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410016).length < 2 ^ (prefixWord ++ tailWord_410016).sum := by decide
  have hdescent : baseEnd_410016 < baseStart_410016 := by decide
  rcases family_descends (prefixWord ++ tailWord_410016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410051 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_410051 : Nat := 118140960795 + 410051 * 2 ^ 59
def prefixEnd_410051 : Nat := 4983230072969 + 3 ^ 40 * 410051 * 2
def baseEnd_410051 : Nat := 187158449650560362023747

theorem tailTrace_410051 : CollatzResearch.WordTrace tailWord_410051 prefixEnd_410051 187158449650560362023747 := by
  unfold tailWord_410051
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955788637462732980446007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9970525758308488653630671 14955788637462732980446007)
  ·
    refine ⟨22433682956194099470669011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14955788637462732980446007 22433682956194099470669011)
    ·
      refine ⟨33650524434291149206003517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22433682956194099470669011 33650524434291149206003517)
      ·
        refine ⟨12618946662859180952251319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33650524434291149206003517 12618946662859180952251319)
        ·
          refine ⟨18928419994288771428376979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12618946662859180952251319 18928419994288771428376979)
          ·
            refine ⟨28392629991433157142565469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18928419994288771428376979 28392629991433157142565469)
            ·
              refine ⟨10647236246787433928462051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28392629991433157142565469 10647236246787433928462051)
              ·
                refine ⟨15970854370181150892693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10647236246787433928462051 15970854370181150892693077)
                ·
                  refine ⟨187158449650560362023747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15970854370181150892693077 187158449650560362023747)
                  ·
                    rfl

theorem cell20_410051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_410051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410051 prefixEnd_410051 := by exact prefixLift 410051
  have htrace : WordTrace (prefixWord ++ tailWord_410051) baseStart_410051 baseEnd_410051 := by
    simpa [prefixWord, tailWord_410051, baseEnd_410051] using wordTrace_append hprefix tailTrace_410051
  have hstable : (prefixWord ++ tailWord_410051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410051).length < 2 ^ (prefixWord ++ tailWord_410051).sum := by decide
  have hdescent : baseEnd_410051 < baseStart_410051 := by decide
  rcases family_descends (prefixWord ++ tailWord_410051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410089 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_410089 : Nat := 118140960795 + 410089 * 2 ^ 59
def prefixEnd_410089 : Nat := 4983230072969 + 3 ^ 40 * 410089 * 2
def baseEnd_410089 : Nat := 187175793886001118756925

theorem tailTrace_410089 : CollatzResearch.WordTrace tailWord_410089 prefixEnd_410089 187175793886001118756925 := by
  unfold tailWord_410089
  simp only [CollatzResearch.WordTrace]
  refine ⟨14957174611325065470329321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9971449740883376980219547 14957174611325065470329321)
  ·
    refine ⟨11217880958493799102746991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14957174611325065470329321 11217880958493799102746991)
    ·
      refine ⟨16826821437740698654120487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11217880958493799102746991 16826821437740698654120487)
      ·
        refine ⟨25240232156611047981180731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16826821437740698654120487 25240232156611047981180731)
        ·
          refine ⟨37860348234916571971771097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25240232156611047981180731 37860348234916571971771097)
          ·
            refine ⟨28395261176187428978828323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37860348234916571971771097 28395261176187428978828323)
            ·
              refine ⟨42592891764281143468242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28395261176187428978828323 42592891764281143468242485)
              ·
                refine ⟨3993083602901357200147733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42592891764281143468242485 3993083602901357200147733)
                ·
                  refine ⟨187175793886001118756925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3993083602901357200147733 187175793886001118756925)
                  ·
                    rfl

theorem cell20_410089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_410089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410089 prefixEnd_410089 := by exact prefixLift 410089
  have htrace : WordTrace (prefixWord ++ tailWord_410089) baseStart_410089 baseEnd_410089 := by
    simpa [prefixWord, tailWord_410089, baseEnd_410089] using wordTrace_append hprefix tailTrace_410089
  have hstable : (prefixWord ++ tailWord_410089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410089).length < 2 ^ (prefixWord ++ tailWord_410089).sum := by decide
  have hdescent : baseEnd_410089 < baseStart_410089 := by decide
  rcases family_descends (prefixWord ++ tailWord_410089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410098 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_410098 : Nat := 118140960795 + 410098 * 2 ^ 59
def prefixEnd_410098 : Nat := 4983230072969 + 3 ^ 40 * 410098 * 2
def baseEnd_410098 : Nat := 187179901731237087456889

theorem tailTrace_410098 : CollatzResearch.WordTrace tailWord_410098 prefixEnd_410098 187179901731237087456889 := by
  unfold tailWord_410098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3739375717073115001851737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9971668578861640004937965 3739375717073115001851737)
  ·
    refine ⟨2804531787804836251388803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3739375717073115001851737 2804531787804836251388803)
    ·
      refine ⟨4206797681707254377083205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2804531787804836251388803 4206797681707254377083205)
      ·
        refine ⟨788774565320110195703101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4206797681707254377083205 788774565320110195703101)
        ·
          refine ⟨295790461995041323388663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 788774565320110195703101 295790461995041323388663)
          ·
            refine ⟨443685692992561985082995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295790461995041323388663 443685692992561985082995)
            ·
              refine ⟨665528539488842977624493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443685692992561985082995 665528539488842977624493)
              ·
                refine ⟨249573202308316116609185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 665528539488842977624493 249573202308316116609185)
                ·
                  refine ⟨187179901731237087456889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249573202308316116609185 187179901731237087456889)
                  ·
                    rfl

theorem cell20_410098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_410098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410098 prefixEnd_410098 := by exact prefixLift 410098
  have htrace : WordTrace (prefixWord ++ tailWord_410098) baseStart_410098 baseEnd_410098 := by
    simpa [prefixWord, tailWord_410098, baseEnd_410098] using wordTrace_append hprefix tailTrace_410098
  have hstable : (prefixWord ++ tailWord_410098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410098).length < 2 ^ (prefixWord ++ tailWord_410098).sum := by decide
  have hdescent : baseEnd_410098 < baseStart_410098 := by decide
  rcases family_descends (prefixWord ++ tailWord_410098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410113 : List Nat := [1, 2, 4, 1, 3, 1, 8]
def baseStart_410113 : Nat := 118140960795 + 410113 * 2 ^ 59
def prefixEnd_410113 : Nat := 4983230072969 + 3 ^ 40 * 410113 * 2
def baseEnd_410113 : Nat := 20798527571107077995203

theorem tailTrace_410113 : CollatzResearch.WordTrace tailWord_410113 prefixEnd_410113 20798527571107077995203 := by
  unfold tailWord_410113
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958049963238117569202993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9972033308825411712801995 14958049963238117569202993)
  ·
    refine ⟨11218537472428588176902245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14958049963238117569202993 11218537472428588176902245)
    ·
      refine ⟨2103475776080360283169171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11218537472428588176902245 2103475776080360283169171)
      ·
        refine ⟨3155213664120540424753757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103475776080360283169171 3155213664120540424753757)
        ·
          refine ⟨1183205124045202659282659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3155213664120540424753757 1183205124045202659282659)
          ·
            refine ⟨1774807686067803988923989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183205124045202659282659 1774807686067803988923989)
            ·
              refine ⟨20798527571107077995203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1774807686067803988923989 20798527571107077995203)
              ·
                rfl

theorem cell20_410113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 8].length) (baseStart_410113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410113 prefixEnd_410113 := by exact prefixLift 410113
  have htrace : WordTrace (prefixWord ++ tailWord_410113) baseStart_410113 baseEnd_410113 := by
    simpa [prefixWord, tailWord_410113, baseEnd_410113] using wordTrace_append hprefix tailTrace_410113
  have hstable : (prefixWord ++ tailWord_410113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410113).length < 2 ^ (prefixWord ++ tailWord_410113).sum := by decide
  have hdescent : baseEnd_410113 < baseStart_410113 := by decide
  rcases family_descends (prefixWord ++ tailWord_410113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410119 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 2]
def baseStart_410119 : Nat := 118140960795 + 410119 * 2 ^ 59
def prefixEnd_410119 : Nat := 4983230072969 + 3 ^ 40 * 410119 * 2
def baseEnd_410119 : Nat := 187189486703454347756803

theorem tailTrace_410119 : CollatzResearch.WordTrace tailWord_410119 prefixEnd_410119 187189486703454347756803 := by
  unfold tailWord_410119
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958268801216380593921411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9972179200810920395947607 14958268801216380593921411)
  ·
    refine ⟨22437403201824570890882117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14958268801216380593921411 22437403201824570890882117)
    ·
      refine ⟨4207013100342107042040397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22437403201824570890882117 4207013100342107042040397)
      ·
        refine ⟨1577629912628290140765149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4207013100342107042040397 1577629912628290140765149)
        ·
          refine ⟨591611217235608802786931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1577629912628290140765149 591611217235608802786931)
          ·
            refine ⟨887416825853413204180397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591611217235608802786931 887416825853413204180397)
            ·
              refine ⟨332781309695029951567649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887416825853413204180397 332781309695029951567649)
              ·
                refine ⟨249585982271272463675737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332781309695029951567649 249585982271272463675737)
                ·
                  refine ⟨187189486703454347756803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249585982271272463675737 187189486703454347756803)
                  ·
                    rfl

theorem cell20_410119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 2].length) (baseStart_410119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410119 prefixEnd_410119 := by exact prefixLift 410119
  have htrace : WordTrace (prefixWord ++ tailWord_410119) baseStart_410119 baseEnd_410119 := by
    simpa [prefixWord, tailWord_410119, baseEnd_410119] using wordTrace_append hprefix tailTrace_410119
  have hstable : (prefixWord ++ tailWord_410119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410119).length < 2 ^ (prefixWord ++ tailWord_410119).sum := by decide
  have hdescent : baseEnd_410119 < baseStart_410119 := by decide
  rcases family_descends (prefixWord ++ tailWord_410119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410123 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 4]
def baseStart_410123 : Nat := 118140960795 + 410123 * 2 ^ 59
def prefixEnd_410123 : Nat := 4983230072969 + 3 ^ 40 * 410123 * 2
def baseEnd_410123 : Nat := 187191312412448111623453

theorem tailTrace_410123 : CollatzResearch.WordTrace tailWord_410123 prefixEnd_410123 187191312412448111623453 := by
  unfold tailWord_410123
  simp only [CollatzResearch.WordTrace]
  refine ⟨14958414693201889277067023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9972276462134592851378015 14958414693201889277067023)
  ·
    refine ⟨22437622039802833915600535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14958414693201889277067023 22437622039802833915600535)
    ·
      refine ⟨33656433059704250873400803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22437622039802833915600535 33656433059704250873400803)
      ·
        refine ⟨50484649589556376310101205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33656433059704250873400803 50484649589556376310101205)
        ·
          refine ⟨1183233974755227569767997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50484649589556376310101205 1183233974755227569767997)
          ·
            refine ⟨443712740533210338662999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1183233974755227569767997 443712740533210338662999)
            ·
              refine ⟨665569110799815507994499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443712740533210338662999 665569110799815507994499)
              ·
                refine ⟨998353666199723261991749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665569110799815507994499 998353666199723261991749)
                ·
                  refine ⟨187191312412448111623453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998353666199723261991749 187191312412448111623453)
                  ·
                    rfl

theorem cell20_410123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_410123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410123 prefixEnd_410123 := by exact prefixLift 410123
  have htrace : WordTrace (prefixWord ++ tailWord_410123) baseStart_410123 baseEnd_410123 := by
    simpa [prefixWord, tailWord_410123, baseEnd_410123] using wordTrace_append hprefix tailTrace_410123
  have hstable : (prefixWord ++ tailWord_410123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410123).length < 2 ^ (prefixWord ++ tailWord_410123).sum := by decide
  have hdescent : baseEnd_410123 < baseStart_410123 := by decide
  rcases family_descends (prefixWord ++ tailWord_410123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410175 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_410175 : Nat := 118140960795 + 410175 * 2 ^ 59
def prefixEnd_410175 : Nat := 4983230072969 + 3 ^ 40 * 410175 * 2
def baseEnd_410175 : Nat := 187215046629367041889907

theorem tailTrace_410175 : CollatzResearch.WordTrace tailWord_410175 prefixEnd_410175 187215046629367041889907 := by
  unfold tailWord_410175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14960311289013502157959979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9973540859342334771973319 14960311289013502157959979)
  ·
    refine ⟨22440466933520253236939969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14960311289013502157959979 22440466933520253236939969)
    ·
      refine ⟨16830350200140189927704977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22440466933520253236939969 16830350200140189927704977)
      ·
        refine ⟨12622762650105142445778733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16830350200140189927704977 12622762650105142445778733)
        ·
          refine ⟨4733535993789428417167025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12622762650105142445778733 4733535993789428417167025)
          ·
            refine ⟨3550151995342071312875269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733535993789428417167025 3550151995342071312875269)
            ·
              refine ⟨665653499126638371164113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3550151995342071312875269 665653499126638371164113)
              ·
                refine ⟨499240124344978778373085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665653499126638371164113 499240124344978778373085)
                ·
                  refine ⟨187215046629367041889907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499240124344978778373085 187215046629367041889907)
                  ·
                    rfl

theorem cell20_410175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_410175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410175 prefixEnd_410175 := by exact prefixLift 410175
  have htrace : WordTrace (prefixWord ++ tailWord_410175) baseStart_410175 baseEnd_410175 := by
    simpa [prefixWord, tailWord_410175, baseEnd_410175] using wordTrace_append hprefix tailTrace_410175
  have hstable : (prefixWord ++ tailWord_410175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410175).length < 2 ^ (prefixWord ++ tailWord_410175).sum := by decide
  have hdescent : baseEnd_410175 < baseStart_410175 := by decide
  rcases family_descends (prefixWord ++ tailWord_410175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410230 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_410230 : Nat := 118140960795 + 410230 * 2 ^ 59
def prefixEnd_410230 : Nat := 4983230072969 + 3 ^ 40 * 410230 * 2
def baseEnd_410230 : Nat := 187240150128031295056349

theorem tailTrace_410230 : CollatzResearch.WordTrace tailWord_410230 prefixEnd_410230 187240150128031295056349 := by
  unfold tailWord_410230
  simp only [CollatzResearch.WordTrace]
  refine ⟨935144831488390409450759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9974878202542831034141429 935144831488390409450759)
  ·
    refine ⟨1402717247232585614176139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 935144831488390409450759 1402717247232585614176139)
    ·
      refine ⟨2104075870848878421264209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1402717247232585614176139 2104075870848878421264209)
      ·
        refine ⟨1578056903136658815948157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2104075870848878421264209 1578056903136658815948157)
        ·
          refine ⟨591771338676247055980559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1578056903136658815948157 591771338676247055980559)
          ·
            refine ⟨887657008014370583970839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591771338676247055980559 887657008014370583970839)
            ·
              refine ⟨1331485512021555875956259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887657008014370583970839 1331485512021555875956259)
              ·
                refine ⟨1997228268032333813934389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331485512021555875956259 1997228268032333813934389)
                ·
                  refine ⟨187240150128031295056349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1997228268032333813934389 187240150128031295056349)
                  ·
                    rfl

theorem cell20_410230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_410230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410230 prefixEnd_410230 := by exact prefixLift 410230
  have htrace : WordTrace (prefixWord ++ tailWord_410230) baseStart_410230 baseEnd_410230 := by
    simpa [prefixWord, tailWord_410230, baseEnd_410230] using wordTrace_append hprefix tailTrace_410230
  have hstable : (prefixWord ++ tailWord_410230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410230).length < 2 ^ (prefixWord ++ tailWord_410230).sum := by decide
  have hdescent : baseEnd_410230 < baseStart_410230 := by decide
  rcases family_descends (prefixWord ++ tailWord_410230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410237 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_410237 : Nat := 118140960795 + 410237 * 2 ^ 59
def prefixEnd_410237 : Nat := 4983230072969 + 3 ^ 40 * 410237 * 2
def baseEnd_410237 : Nat := 187243345118770381822987

theorem tailTrace_410237 : CollatzResearch.WordTrace tailWord_410237 prefixEnd_410237 187243345118770381822987 := by
  unfold tailWord_410237
  simp only [CollatzResearch.WordTrace]
  refine ⟨14962572614788886746716965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9975048409859257831144643 14962572614788886746716965)
  ·
    refine ⟨2805482365272916265009431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14962572614788886746716965 2805482365272916265009431)
    ·
      refine ⟨4208223547909374397514147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805482365272916265009431 4208223547909374397514147)
      ·
        refine ⟨6312335321864061596271221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208223547909374397514147 6312335321864061596271221)
        ·
          refine ⟨591781436424755774650427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6312335321864061596271221 591781436424755774650427)
          ·
            refine ⟨887672154637133661975641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591781436424755774650427 887672154637133661975641)
            ·
              refine ⟨665754115977850246481731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887672154637133661975641 665754115977850246481731)
              ·
                refine ⟨998631173966775369722597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665754115977850246481731 998631173966775369722597)
                ·
                  refine ⟨187243345118770381822987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998631173966775369722597 187243345118770381822987)
                  ·
                    rfl

theorem cell20_410237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_410237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410237 prefixEnd_410237 := by exact prefixLift 410237
  have htrace : WordTrace (prefixWord ++ tailWord_410237) baseStart_410237 baseEnd_410237 := by
    simpa [prefixWord, tailWord_410237, baseEnd_410237] using wordTrace_append hprefix tailTrace_410237
  have hstable : (prefixWord ++ tailWord_410237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410237).length < 2 ^ (prefixWord ++ tailWord_410237).sum := by decide
  have hdescent : baseEnd_410237 < baseStart_410237 := by decide
  rcases family_descends (prefixWord ++ tailWord_410237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410303 : List Nat := [1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_410303 : Nat := 118140960795 + 410303 * 2 ^ 59
def prefixEnd_410303 : Nat := 4983230072969 + 3 ^ 40 * 410303 * 2
def baseEnd_410303 : Nat := 62424489772389161874239

theorem tailTrace_410303 : CollatzResearch.WordTrace tailWord_410303 prefixEnd_410303 62424489772389161874239 := by
  unfold tailWord_410303
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964979832549780018619563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9976653221699853345746375 14964979832549780018619563)
  ·
    refine ⟨22447469748824670027929345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14964979832549780018619563 22447469748824670027929345)
    ·
      refine ⟨16835602311618502520947009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22447469748824670027929345 16835602311618502520947009)
      ·
        refine ⟨12626701733713876890710257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16835602311618502520947009 12626701733713876890710257)
        ·
          refine ⟨9470026300285407668032693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12626701733713876890710257 9470026300285407668032693)
          ·
            refine ⟨887814965651756968878065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9470026300285407668032693 887814965651756968878065)
            ·
              refine ⟨665861224238817726658549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887814965651756968878065 665861224238817726658549)
              ·
                refine ⟨62424489772389161874239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665861224238817726658549 62424489772389161874239)
                ·
                  rfl

theorem cell20_410303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_410303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410303 prefixEnd_410303 := by exact prefixLift 410303
  have htrace : WordTrace (prefixWord ++ tailWord_410303) baseStart_410303 baseEnd_410303 := by
    simpa [prefixWord, tailWord_410303, baseEnd_410303] using wordTrace_append hprefix tailTrace_410303
  have hstable : (prefixWord ++ tailWord_410303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410303).length < 2 ^ (prefixWord ++ tailWord_410303).sum := by decide
  have hdescent : baseEnd_410303 < baseStart_410303 := by decide
  rcases family_descends (prefixWord ++ tailWord_410303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410344 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_410344 : Nat := 118140960795 + 410344 * 2 ^ 59
def prefixEnd_410344 : Nat := 4983230072969 + 3 ^ 40 * 410344 * 2
def baseEnd_410344 : Nat := 187292182834353565255883

theorem tailTrace_410344 : CollatzResearch.WordTrace tailWord_410344 prefixEnd_410344 187292182834353565255883 := by
  unfold tailWord_410344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483237612700622010431043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9977650150267496013908057 7483237612700622010431043)
  ·
    refine ⟨11224856419050933015646565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7483237612700622010431043 11224856419050933015646565)
    ·
      refine ⟨2104660578572049940433731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11224856419050933015646565 2104660578572049940433731)
      ·
        refine ⟨3156990867858074910650597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104660578572049940433731 3156990867858074910650597)
        ·
          refine ⟨591935787723389045746987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3156990867858074910650597 591935787723389045746987)
          ·
            refine ⟨887903681585083568620481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591935787723389045746987 887903681585083568620481)
            ·
              refine ⟨665927761188812676465361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887903681585083568620481 665927761188812676465361)
              ·
                refine ⟨499445820891609507349021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665927761188812676465361 499445820891609507349021)
                ·
                  refine ⟨187292182834353565255883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499445820891609507349021 187292182834353565255883)
                  ·
                    rfl

theorem cell20_410344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_410344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410344 prefixEnd_410344 := by exact prefixLift 410344
  have htrace : WordTrace (prefixWord ++ tailWord_410344) baseStart_410344 baseEnd_410344 := by
    simpa [prefixWord, tailWord_410344, baseEnd_410344] using wordTrace_append hprefix tailTrace_410344
  have hstable : (prefixWord ++ tailWord_410344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410344).length < 2 ^ (prefixWord ++ tailWord_410344).sum := by decide
  have hdescent : baseEnd_410344 < baseStart_410344 := by decide
  rcases family_descends (prefixWord ++ tailWord_410344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410351 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 2]
def baseStart_410351 : Nat := 118140960795 + 410351 * 2 ^ 59
def prefixEnd_410351 : Nat := 4983230072969 + 3 ^ 40 * 410351 * 2
def baseEnd_410351 : Nat := 187295377825092652022521

theorem tailTrace_410351 : CollatzResearch.WordTrace tailWord_410351 prefixEnd_410351 187295377825092652022521 := by
  unfold tailWord_410351
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966730536375884216366907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9977820357583922810911271 14966730536375884216366907)
  ·
    refine ⟨22450095804563826324550361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14966730536375884216366907 22450095804563826324550361)
    ·
      refine ⟨16837571853422869743412771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22450095804563826324550361 16837571853422869743412771)
      ·
        refine ⟨25256357780134304615119157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16837571853422869743412771 25256357780134304615119157)
        ·
          refine ⟨2367783541887591057667421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25256357780134304615119157 2367783541887591057667421)
          ·
            refine ⟨887918828207846646625283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2367783541887591057667421 887918828207846646625283)
            ·
              refine ⟨1331878242311769969937925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887918828207846646625283 1331878242311769969937925)
              ·
                refine ⟨249727170433456869363361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1331878242311769969937925 249727170433456869363361)
                ·
                  refine ⟨187295377825092652022521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249727170433456869363361 187295377825092652022521)
                  ·
                    rfl

theorem cell20_410351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 2].length) (baseStart_410351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410351 prefixEnd_410351 := by exact prefixLift 410351
  have htrace : WordTrace (prefixWord ++ tailWord_410351) baseStart_410351 baseEnd_410351 := by
    simpa [prefixWord, tailWord_410351, baseEnd_410351] using wordTrace_append hprefix tailTrace_410351
  have hstable : (prefixWord ++ tailWord_410351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410351).length < 2 ^ (prefixWord ++ tailWord_410351).sum := by decide
  have hdescent : baseEnd_410351 < baseStart_410351 := by decide
  rcases family_descends (prefixWord ++ tailWord_410351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410355 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_410355 : Nat := 118140960795 + 410355 * 2 ^ 59
def prefixEnd_410355 : Nat := 4983230072969 + 3 ^ 40 * 410355 * 2
def baseEnd_410355 : Nat := 187297203534086415889171

theorem tailTrace_410355 : CollatzResearch.WordTrace tailWord_410355 prefixEnd_410355 187297203534086415889171 := by
  unfold tailWord_410355
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966876428361392899512519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9977917618907595266341679 14966876428361392899512519)
  ·
    refine ⟨22450314642542089349268779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14966876428361392899512519 22450314642542089349268779)
    ·
      refine ⟨33675471963813134023903169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22450314642542089349268779 33675471963813134023903169)
      ·
        refine ⟨25256603972859850517927377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33675471963813134023903169 25256603972859850517927377)
        ·
          refine ⟨18942452979644887888445533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25256603972859850517927377 18942452979644887888445533)
          ·
            refine ⟨7103419867366832958167075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18942452979644887888445533 7103419867366832958167075)
            ·
              refine ⟨10655129801050249437250613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103419867366832958167075 10655129801050249437250613)
              ·
                refine ⟨998918418848460884742245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10655129801050249437250613 998918418848460884742245)
                ·
                  refine ⟨187297203534086415889171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998918418848460884742245 187297203534086415889171)
                  ·
                    rfl

theorem cell20_410355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_410355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410355 prefixEnd_410355 := by exact prefixLift 410355
  have htrace : WordTrace (prefixWord ++ tailWord_410355) baseStart_410355 baseEnd_410355 := by
    simpa [prefixWord, tailWord_410355, baseEnd_410355] using wordTrace_append hprefix tailTrace_410355
  have hstable : (prefixWord ++ tailWord_410355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410355).length < 2 ^ (prefixWord ++ tailWord_410355).sum := by decide
  have hdescent : baseEnd_410355 < baseStart_410355 := by decide
  rcases family_descends (prefixWord ++ tailWord_410355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410372 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_410372 : Nat := 118140960795 + 410372 * 2 ^ 59
def prefixEnd_410372 : Nat := 4983230072969 + 3 ^ 40 * 410372 * 2
def baseEnd_410372 : Nat := 187304962797309912322435

theorem tailTrace_410372 : CollatzResearch.WordTrace tailWord_410372 prefixEnd_410372 187304962797309912322435 := by
  unfold tailWord_410372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483748234649902401440685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9978330979533203201920913 7483748234649902401440685)
  ·
    refine ⟨2806405587993713400540257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7483748234649902401440685 2806405587993713400540257)
    ·
      refine ⟨2104804190995285050405193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806405587993713400540257 2104804190995285050405193)
      ·
        refine ⟨1578603143246463787803895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2104804190995285050405193 1578603143246463787803895)
        ·
          refine ⟨2367904714869695681705843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578603143246463787803895 2367904714869695681705843)
          ·
            refine ⟨3551857072304543522558765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367904714869695681705843 3551857072304543522558765)
            ·
              refine ⟨1331946402114203820959537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3551857072304543522558765 1331946402114203820959537)
              ·
                refine ⟨998959801585652865719653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331946402114203820959537 998959801585652865719653)
                ·
                  refine ⟨187304962797309912322435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 998959801585652865719653 187304962797309912322435)
                  ·
                    rfl

theorem cell20_410372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_410372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410372 prefixEnd_410372 := by exact prefixLift 410372
  have htrace : WordTrace (prefixWord ++ tailWord_410372) baseStart_410372 baseEnd_410372 := by
    simpa [prefixWord, tailWord_410372, baseEnd_410372] using wordTrace_append hprefix tailTrace_410372
  have hstable : (prefixWord ++ tailWord_410372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410372).length < 2 ^ (prefixWord ++ tailWord_410372).sum := by decide
  have hdescent : baseEnd_410372 < baseStart_410372 := by decide
  rcases family_descends (prefixWord ++ tailWord_410372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410389 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 2]
def baseStart_410389 : Nat := 118140960795 + 410389 * 2 ^ 59
def prefixEnd_410389 : Nat := 4983230072969 + 3 ^ 40 * 410389 * 2
def baseEnd_410389 : Nat := 187312722060533408755699

theorem tailTrace_410389 : CollatzResearch.WordTrace tailWord_410389 prefixEnd_410389 187312722060533408755699 := by
  unfold tailWord_410389
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968116510238216706250221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9978744340158811137500147 14968116510238216706250221)
  ·
    refine ⟨5613043691339331264843833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14968116510238216706250221 5613043691339331264843833)
    ·
      refine ⟨4209782768504498448632875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5613043691339331264843833 4209782768504498448632875)
      ·
        refine ⟨6314674152756747672949313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209782768504498448632875 6314674152756747672949313)
        ·
          refine ⟨4736005614567560754711985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6314674152756747672949313 4736005614567560754711985)
          ·
            refine ⟨3552004210925670566033989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4736005614567560754711985 3552004210925670566033989)
            ·
              refine ⟨666000789548563231131373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3552004210925670566033989 666000789548563231131373)
              ·
                refine ⟨249750296080711211674265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666000789548563231131373 249750296080711211674265)
                ·
                  refine ⟨187312722060533408755699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249750296080711211674265 187312722060533408755699)
                  ·
                    rfl

theorem cell20_410389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_410389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410389 prefixEnd_410389 := by exact prefixLift 410389
  have htrace : WordTrace (prefixWord ++ tailWord_410389) baseStart_410389 baseEnd_410389 := by
    simpa [prefixWord, tailWord_410389, baseEnd_410389] using wordTrace_append hprefix tailTrace_410389
  have hstable : (prefixWord ++ tailWord_410389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410389).length < 2 ^ (prefixWord ++ tailWord_410389).sum := by decide
  have hdescent : baseEnd_410389 < baseStart_410389 := by decide
  rcases family_descends (prefixWord ++ tailWord_410389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410430 : List Nat := [4, 2, 1, 2, 4, 1, 2, 4]
def baseStart_410430 : Nat := 118140960795 + 410430 * 2 ^ 59
def prefixEnd_410430 : Nat := 4983230072969 + 3 ^ 40 * 410430 * 2
def baseEnd_410430 : Nat := 62443811859239829462955

theorem tailTrace_410430 : CollatzResearch.WordTrace tailWord_410430 prefixEnd_410430 62443811859239829462955 := by
  unfold tailWord_410430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871201487886210088561593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9979741268726453805661829 1871201487886210088561593)
  ·
    refine ⟨1403401115914657566421195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1871201487886210088561593 1403401115914657566421195)
    ·
      refine ⟨2105101673871986349631793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403401115914657566421195 2105101673871986349631793)
      ·
        refine ⟨1578826255403989762223845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105101673871986349631793 1578826255403989762223845)
        ·
          refine ⟨296029922888248080416971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1578826255403989762223845 296029922888248080416971)
          ·
            refine ⟨444044884332372120625457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296029922888248080416971 444044884332372120625457)
            ·
              refine ⟨333033663249279090469093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444044884332372120625457 333033663249279090469093)
              ·
                refine ⟨62443811859239829462955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333033663249279090469093 62443811859239829462955)
                ·
                  rfl

theorem cell20_410430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_410430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410430 prefixEnd_410430 := by exact prefixLift 410430
  have htrace : WordTrace (prefixWord ++ tailWord_410430) baseStart_410430 baseEnd_410430 := by
    simpa [prefixWord, tailWord_410430, baseEnd_410430] using wordTrace_append hprefix tailTrace_410430
  have hstable : (prefixWord ++ tailWord_410430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410430).length < 2 ^ (prefixWord ++ tailWord_410430).sum := by decide
  have hdescent : baseEnd_410430 < baseStart_410430 := by decide
  rcases family_descends (prefixWord ++ tailWord_410430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410444 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 2]
def baseStart_410444 : Nat := 118140960795 + 410444 * 2 ^ 59
def prefixEnd_410444 : Nat := 4983230072969 + 3 ^ 40 * 410444 * 2
def baseEnd_410444 : Nat := 187337825559197661922141

theorem tailTrace_410444 : CollatzResearch.WordTrace tailWord_410444 prefixEnd_410444 187337825559197661922141 := by
  unfold tailWord_410444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485061262519480549751193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9980081683359307399668257 7485061262519480549751193)
  ·
    refine ⟨5613795946889610412313395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7485061262519480549751193 5613795946889610412313395)
    ·
      refine ⟨8420693920334415618470093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5613795946889610412313395 8420693920334415618470093)
      ·
        refine ⟨3157760220125405856926285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8420693920334415618470093 3157760220125405856926285)
        ·
          refine ⟨1184160082547027196347357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3157760220125405856926285 1184160082547027196347357)
          ·
            refine ⟨444060030955135198630259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1184160082547027196347357 444060030955135198630259)
            ·
              refine ⟨666090046432702797945389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444060030955135198630259 666090046432702797945389)
              ·
                refine ⟨249783767412263549229521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666090046432702797945389 249783767412263549229521)
                ·
                  refine ⟨187337825559197661922141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249783767412263549229521 187337825559197661922141)
                  ·
                    rfl

theorem cell20_410444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_410444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410444 prefixEnd_410444 := by exact prefixLift 410444
  have htrace : WordTrace (prefixWord ++ tailWord_410444) baseStart_410444 baseEnd_410444 := by
    simpa [prefixWord, tailWord_410444, baseEnd_410444] using wordTrace_append hprefix tailTrace_410444
  have hstable : (prefixWord ++ tailWord_410444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410444).length < 2 ^ (prefixWord ++ tailWord_410444).sum := by decide
  have hdescent : baseEnd_410444 < baseStart_410444 := by decide
  rcases family_descends (prefixWord ++ tailWord_410444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410455 : List Nat := [1, 1, 3, 2, 4, 3, 6]
def baseStart_410455 : Nat := 118140960795 + 410455 * 2 ^ 59
def prefixEnd_410455 : Nat := 4983230072969 + 3 ^ 40 * 410455 * 2
def baseEnd_410455 : Nat := 20815871806547834728381

theorem tailTrace_410455 : CollatzResearch.WordTrace tailWord_410455 prefixEnd_410455 20815871806547834728381 := by
  unfold tailWord_410455
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970523727999109978152819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9980349151999406652101879 14970523727999109978152819)
  ·
    refine ⟨22455785591998664967229229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14970523727999109978152819 22455785591998664967229229)
    ·
      refine ⟨8420919596999499362710961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22455785591998664967229229 8420919596999499362710961)
      ·
        refine ⟨6315689697749624522033221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8420919596999499362710961 6315689697749624522033221)
        ·
          refine ⟨1184191818328054597881229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6315689697749624522033221 1184191818328054597881229)
          ·
            refine ⟨444071931873020474205461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1184191818328054597881229 444071931873020474205461)
            ·
              refine ⟨20815871806547834728381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444071931873020474205461 20815871806547834728381)
              ·
                rfl

theorem cell20_410455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 6].length) (baseStart_410455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410455 prefixEnd_410455 := by exact prefixLift 410455
  have htrace : WordTrace (prefixWord ++ tailWord_410455) baseStart_410455 baseEnd_410455 := by
    simpa [prefixWord, tailWord_410455, baseEnd_410455] using wordTrace_append hprefix tailTrace_410455
  have hstable : (prefixWord ++ tailWord_410455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410455).length < 2 ^ (prefixWord ++ tailWord_410455).sum := by decide
  have hdescent : baseEnd_410455 < baseStart_410455 := by decide
  rcases family_descends (prefixWord ++ tailWord_410455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410517 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_410517 : Nat := 118140960795 + 410517 * 2 ^ 59
def prefixEnd_410517 : Nat := 4983230072969 + 3 ^ 40 * 410517 * 2
def baseEnd_410517 : Nat := 187371144748333852488509

theorem tailTrace_410517 : CollatzResearch.WordTrace tailWord_410517 prefixEnd_410517 187371144748333852488509 := by
  unfold tailWord_410517
  simp only [CollatzResearch.WordTrace]
  refine ⟨14972785053774494566909805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9981856702516329711273203 14972785053774494566909805)
  ·
    refine ⟨5614794395165435462591177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14972785053774494566909805 5614794395165435462591177)
    ·
      refine ⟨4211095796374076596943383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5614794395165435462591177 4211095796374076596943383)
      ·
        refine ⟨6316643694561114895415075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4211095796374076596943383 6316643694561114895415075)
        ·
          refine ⟨9474965541841672343122613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6316643694561114895415075 9474965541841672343122613)
          ·
            refine ⟨888278019547656782167745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9474965541841672343122613 888278019547656782167745)
            ·
              refine ⟨666208514660742586625809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888278019547656782167745 666208514660742586625809)
              ·
                refine ⟨499656385995556939969357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666208514660742586625809 499656385995556939969357)
                ·
                  refine ⟨187371144748333852488509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499656385995556939969357 187371144748333852488509)
                  ·
                    rfl

theorem cell20_410517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_410517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410517 prefixEnd_410517 := by exact prefixLift 410517
  have htrace : WordTrace (prefixWord ++ tailWord_410517) baseStart_410517 baseEnd_410517 := by
    simpa [prefixWord, tailWord_410517, baseEnd_410517] using wordTrace_append hprefix tailTrace_410517
  have hstable : (prefixWord ++ tailWord_410517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410517).length < 2 ^ (prefixWord ++ tailWord_410517).sum := by decide
  have hdescent : baseEnd_410517 < baseStart_410517 := by decide
  rcases family_descends (prefixWord ++ tailWord_410517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410607 : List Nat := [1, 1, 2, 1, 4, 3, 4, 4]
def baseStart_410607 : Nat := 118140960795 + 410607 * 2 ^ 59
def prefixEnd_410607 : Nat := 4983230072969 + 3 ^ 40 * 410607 * 2
def baseEnd_410607 : Nat := 62470741066897846496047

theorem tailTrace_410607 : CollatzResearch.WordTrace tailWord_410607 prefixEnd_410607 62470741066897846496047 := by
  unfold tailWord_410607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14976067623448439937686075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9984045082298959958457383 14976067623448439937686075)
  ·
    refine ⟨22464101435172659906529113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14976067623448439937686075 22464101435172659906529113)
    ·
      refine ⟨16848076076379494929896835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22464101435172659906529113 16848076076379494929896835)
      ·
        refine ⟨25272114114569242394845253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16848076076379494929896835 25272114114569242394845253)
        ·
          refine ⟨4738521396481732949033485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25272114114569242394845253 4738521396481732949033485)
          ·
            refine ⟨1776945523680649855887557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4738521396481732949033485 1776945523680649855887557)
            ·
              refine ⟨333177285690121847978917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1776945523680649855887557 333177285690121847978917)
              ·
                refine ⟨62470741066897846496047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333177285690121847978917 62470741066897846496047)
                ·
                  rfl

theorem cell20_410607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_410607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410607 prefixEnd_410607 := by exact prefixLift 410607
  have htrace : WordTrace (prefixWord ++ tailWord_410607) baseStart_410607 baseEnd_410607 := by
    simpa [prefixWord, tailWord_410607, baseEnd_410607] using wordTrace_append hprefix tailTrace_410607
  have hstable : (prefixWord ++ tailWord_410607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410607).length < 2 ^ (prefixWord ++ tailWord_410607).sum := by decide
  have hdescent : baseEnd_410607 < baseStart_410607 := by decide
  rcases family_descends (prefixWord ++ tailWord_410607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410634 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_410634 : Nat := 118140960795 + 410634 * 2 ^ 59
def prefixEnd_410634 : Nat := 4983230072969 + 3 ^ 40 * 410634 * 2
def baseEnd_410634 : Nat := 187424546736401445588031

theorem tailTrace_410634 : CollatzResearch.WordTrace tailWord_410634 prefixEnd_410634 187424546736401445588031 := by
  unfold tailWord_410634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744263098587655887229739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9984701596233749032612637 3744263098587655887229739)
  ·
    refine ⟨5616394647881483830844609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3744263098587655887229739 5616394647881483830844609)
    ·
      refine ⟨4212295985911112873133457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5616394647881483830844609 4212295985911112873133457)
      ·
        refine ⟨3159221989433334654850093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4212295985911112873133457 3159221989433334654850093)
        ·
          refine ⟨1184708246037500495568785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3159221989433334654850093 1184708246037500495568785)
          ·
            refine ⟨888531184528125371676589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184708246037500495568785 888531184528125371676589)
            ·
              refine ⟨333199194198047014378721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 888531184528125371676589 333199194198047014378721)
              ·
                refine ⟨249899395648535260784041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333199194198047014378721 249899395648535260784041)
                ·
                  refine ⟨187424546736401445588031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249899395648535260784041 187424546736401445588031)
                  ·
                    rfl

theorem cell20_410634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_410634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410634 prefixEnd_410634 := by exact prefixLift 410634
  have htrace : WordTrace (prefixWord ++ tailWord_410634) baseStart_410634 baseEnd_410634 := by
    simpa [prefixWord, tailWord_410634, baseEnd_410634] using wordTrace_append hprefix tailTrace_410634
  have hstable : (prefixWord ++ tailWord_410634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410634).length < 2 ^ (prefixWord ++ tailWord_410634).sum := by decide
  have hdescent : baseEnd_410634 < baseStart_410634 := by decide
  rcases family_descends (prefixWord ++ tailWord_410634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410638 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_410638 : Nat := 118140960795 + 410638 * 2 ^ 59
def prefixEnd_410638 : Nat := 4983230072969 + 3 ^ 40 * 410638 * 2
def baseEnd_410638 : Nat := 187426372445395209454681

theorem tailTrace_410638 : CollatzResearch.WordTrace tailWord_410638 prefixEnd_410638 187426372445395209454681 := by
  unfold tailWord_410638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872149785792016529008071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9984798857557421488043045 1872149785792016529008071)
  ·
    refine ⟨2808224678688024793512107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1872149785792016529008071 2808224678688024793512107)
    ·
      refine ⟨4212337018032037190268161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808224678688024793512107 4212337018032037190268161)
      ·
        refine ⟨3159252763524027892701121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4212337018032037190268161 3159252763524027892701121)
        ·
          refine ⟨2369439572643020919525841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3159252763524027892701121 2369439572643020919525841)
          ·
            refine ⟨1777079679482265689644381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2369439572643020919525841 1777079679482265689644381)
            ·
              refine ⟨666404879805849633616643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1777079679482265689644381 666404879805849633616643)
              ·
                refine ⟨999607319708774450424965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666404879805849633616643 999607319708774450424965)
                ·
                  refine ⟨187426372445395209454681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999607319708774450424965 187426372445395209454681)
                  ·
                    rfl

theorem cell20_410638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_410638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410638 prefixEnd_410638 := by exact prefixLift 410638
  have htrace : WordTrace (prefixWord ++ tailWord_410638) baseStart_410638 baseEnd_410638 := by
    simpa [prefixWord, tailWord_410638, baseEnd_410638] using wordTrace_append hprefix tailTrace_410638
  have hstable : (prefixWord ++ tailWord_410638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410638).length < 2 ^ (prefixWord ++ tailWord_410638).sum := by decide
  have hdescent : baseEnd_410638 < baseStart_410638 := by decide
  rcases family_descends (prefixWord ++ tailWord_410638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410645 : List Nat := [1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_410645 : Nat := 118140960795 + 410645 * 2 ^ 59
def prefixEnd_410645 : Nat := 4983230072969 + 3 ^ 40 * 410645 * 2
def baseEnd_410645 : Nat := 62476522478711432073773

theorem tailTrace_410645 : CollatzResearch.WordTrace tailWord_410645 prefixEnd_410645 62476522478711432073773 := by
  unfold tailWord_410645
  simp only [CollatzResearch.WordTrace]
  refine ⟨14977453597310772427569389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9984969064873848285046259 14977453597310772427569389)
  ·
    refine ⟨5616545098991539660338521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14977453597310772427569389 5616545098991539660338521)
    ·
      refine ⟨4212408824243654745253891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5616545098991539660338521 4212408824243654745253891)
      ·
        refine ⟨6318613236365482117880837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212408824243654745253891 6318613236365482117880837)
        ·
          refine ⟨1184739981818527897102657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6318613236365482117880837 1184739981818527897102657)
          ·
            refine ⟨888554986363895922826993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184739981818527897102657 888554986363895922826993)
            ·
              refine ⟨666416239772921942120245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888554986363895922826993 666416239772921942120245)
              ·
                refine ⟨62476522478711432073773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 666416239772921942120245 62476522478711432073773)
                ·
                  rfl

theorem cell20_410645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_410645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410645 prefixEnd_410645 := by exact prefixLift 410645
  have htrace : WordTrace (prefixWord ++ tailWord_410645) baseStart_410645 baseEnd_410645 := by
    simpa [prefixWord, tailWord_410645, baseEnd_410645] using wordTrace_append hprefix tailTrace_410645
  have hstable : (prefixWord ++ tailWord_410645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410645).length < 2 ^ (prefixWord ++ tailWord_410645).sum := by decide
  have hdescent : baseEnd_410645 < baseStart_410645 := by decide
  rcases family_descends (prefixWord ++ tailWord_410645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410648 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_410648 : Nat := 118140960795 + 410648 * 2 ^ 59
def prefixEnd_410648 : Nat := 4983230072969 + 3 ^ 40 * 410648 * 2
def baseEnd_410648 : Nat := 187430936717879619121307

theorem tailTrace_410648 : CollatzResearch.WordTrace tailWord_410648 prefixEnd_410648 187430936717879619121307 := by
  unfold tailWord_410648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7488781508149951969964299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9985042010866602626619065 7488781508149951969964299)
  ·
    refine ⟨11233172262224927954946449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7488781508149951969964299 11233172262224927954946449)
    ·
      refine ⟨8424879196668695966209837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11233172262224927954946449 8424879196668695966209837)
      ·
        refine ⟨3159329698750760987328689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8424879196668695966209837 3159329698750760987328689)
        ·
          refine ⟨2369497274063070740496517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3159329698750760987328689 2369497274063070740496517)
          ·
            refine ⟨444280738886825763843097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2369497274063070740496517 444280738886825763843097)
            ·
              refine ⟨333210554165119322882323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444280738886825763843097 333210554165119322882323)
              ·
                refine ⟨499815831247678984323485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333210554165119322882323 499815831247678984323485)
                ·
                  refine ⟨187430936717879619121307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499815831247678984323485 187430936717879619121307)
                  ·
                    rfl

theorem cell20_410648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_410648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410648 prefixEnd_410648 := by exact prefixLift 410648
  have htrace : WordTrace (prefixWord ++ tailWord_410648) baseStart_410648 baseEnd_410648 := by
    simpa [prefixWord, tailWord_410648, baseEnd_410648] using wordTrace_append hprefix tailTrace_410648
  have hstable : (prefixWord ++ tailWord_410648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410648).length < 2 ^ (prefixWord ++ tailWord_410648).sum := by decide
  have hdescent : baseEnd_410648 < baseStart_410648 := by decide
  rcases family_descends (prefixWord ++ tailWord_410648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410686 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_410686 : Nat := 118140960795 + 410686 * 2 ^ 59
def prefixEnd_410686 : Nat := 4983230072969 + 3 ^ 40 * 410686 * 2
def baseEnd_410686 : Nat := 187448280953320375854485

theorem tailTrace_410686 : CollatzResearch.WordTrace tailWord_410686 prefixEnd_410686 187448280953320375854485 := by
  unfold tailWord_410686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872368623770279553726489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9985965993441490953207941 1872368623770279553726489)
  ·
    refine ⟨1404276467827709665294867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1872368623770279553726489 1404276467827709665294867)
    ·
      refine ⟨2106414701741564497942301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1404276467827709665294867 2106414701741564497942301)
      ·
        refine ⟨789905513153086686728363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2106414701741564497942301 789905513153086686728363)
        ·
          refine ⟨1184858269729630030092545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789905513153086686728363 1184858269729630030092545)
          ·
            refine ⟨888643702297222522569409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184858269729630030092545 888643702297222522569409)
            ·
              refine ⟨666482776722916891927057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888643702297222522569409 666482776722916891927057)
              ·
                refine ⟨499862082542187668945293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666482776722916891927057 499862082542187668945293)
                ·
                  refine ⟨187448280953320375854485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499862082542187668945293 187448280953320375854485)
                  ·
                    rfl

theorem cell20_410686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_410686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410686 prefixEnd_410686 := by exact prefixLift 410686
  have htrace : WordTrace (prefixWord ++ tailWord_410686) baseStart_410686 baseEnd_410686 := by
    simpa [prefixWord, tailWord_410686, baseEnd_410686] using wordTrace_append hprefix tailTrace_410686
  have hstable : (prefixWord ++ tailWord_410686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410686).length < 2 ^ (prefixWord ++ tailWord_410686).sum := by decide
  have hdescent : baseEnd_410686 < baseStart_410686 := by decide
  rcases family_descends (prefixWord ++ tailWord_410686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410689 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 2]
def baseStart_410689 : Nat := 118140960795 + 410689 * 2 ^ 59
def prefixEnd_410689 : Nat := 4983230072969 + 3 ^ 40 * 410689 * 2
def baseEnd_410689 : Nat := 187449650235065698754473

theorem tailTrace_410689 : CollatzResearch.WordTrace tailWord_410689 prefixEnd_410689 187449650235065698754473 := by
  unfold tailWord_410689
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979058409151367942171121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986038939434245294780747 14979058409151367942171121)
  ·
    refine ⟨11234293806863525956628341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14979058409151367942171121 11234293806863525956628341)
    ·
      refine ⟨1053215044393455558433907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11234293806863525956628341 1053215044393455558433907)
      ·
        refine ⟨1579822566590183337650861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053215044393455558433907 1579822566590183337650861)
        ·
          refine ⟨592433462471318751619073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1579822566590183337650861 592433462471318751619073)
          ·
            refine ⟨444325096853489063714305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592433462471318751619073 444325096853489063714305)
            ·
              refine ⟨333243822640116797785729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444325096853489063714305 333243822640116797785729)
              ·
                refine ⟨249932866980087598339297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333243822640116797785729 249932866980087598339297)
                ·
                  refine ⟨187449650235065698754473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249932866980087598339297 187449650235065698754473)
                  ·
                    rfl

theorem cell20_410689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_410689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410689 prefixEnd_410689 := by exact prefixLift 410689
  have htrace : WordTrace (prefixWord ++ tailWord_410689) baseStart_410689 baseEnd_410689 := by
    simpa [prefixWord, tailWord_410689, baseEnd_410689] using wordTrace_append hprefix tailTrace_410689
  have hstable : (prefixWord ++ tailWord_410689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410689).length < 2 ^ (prefixWord ++ tailWord_410689).sum := by decide
  have hdescent : baseEnd_410689 < baseStart_410689 := by decide
  rcases family_descends (prefixWord ++ tailWord_410689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410693 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 2]
def baseStart_410693 : Nat := 118140960795 + 410693 * 2 ^ 59
def prefixEnd_410693 : Nat := 4983230072969 + 3 ^ 40 * 410693 * 2
def baseEnd_410693 : Nat := 187451475944059462621123

theorem tailTrace_410693 : CollatzResearch.WordTrace tailWord_410693 prefixEnd_410693 187451475944059462621123 := by
  unfold tailWord_410693
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979204301136876625316733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986136200757917750211155 14979204301136876625316733)
  ·
    refine ⟨5617201612926328734493775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14979204301136876625316733 5617201612926328734493775)
    ·
      refine ⟨8425802419389493101740663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617201612926328734493775 8425802419389493101740663)
      ·
        refine ⟨12638703629084239652610995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8425802419389493101740663 12638703629084239652610995)
        ·
          refine ⟨18958055443626359478916493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12638703629084239652610995 18958055443626359478916493)
          ·
            refine ⟨7109270791359884804593685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18958055443626359478916493 7109270791359884804593685)
            ·
              refine ⟨333247068344994600215329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7109270791359884804593685 333247068344994600215329)
              ·
                refine ⟨249935301258745950161497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333247068344994600215329 249935301258745950161497)
                ·
                  refine ⟨187451475944059462621123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249935301258745950161497 187451475944059462621123)
                  ·
                    rfl

theorem cell20_410693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_410693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410693 prefixEnd_410693 := by exact prefixLift 410693
  have htrace : WordTrace (prefixWord ++ tailWord_410693) baseStart_410693 baseEnd_410693 := by
    simpa [prefixWord, tailWord_410693, baseEnd_410693] using wordTrace_append hprefix tailTrace_410693
  have hstable : (prefixWord ++ tailWord_410693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410693).length < 2 ^ (prefixWord ++ tailWord_410693).sum := by decide
  have hdescent : baseEnd_410693 < baseStart_410693 := by decide
  rcases family_descends (prefixWord ++ tailWord_410693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410710 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_410710 : Nat := 118140960795 + 410710 * 2 ^ 59
def prefixEnd_410710 : Nat := 4983230072969 + 3 ^ 40 * 410710 * 2
def baseEnd_410710 : Nat := 187459235207282959054387

theorem tailTrace_410710 : CollatzResearch.WordTrace tailWord_410710 prefixEnd_410710 187459235207282959054387 := by
  unfold tailWord_410710
  simp only [CollatzResearch.WordTrace]
  refine ⟨936239021379705533042849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9986549561383525685790389 936239021379705533042849)
  ·
    refine ⟨702179266034779149782137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 936239021379705533042849 702179266034779149782137)
    ·
      refine ⟨526634449526084362336603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702179266034779149782137 526634449526084362336603)
      ·
        refine ⟨789951674289126543504905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526634449526084362336603 789951674289126543504905)
        ·
          refine ⟨592463755716844907628679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789951674289126543504905 592463755716844907628679)
          ·
            refine ⟨888695633575267361443019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592463755716844907628679 888695633575267361443019)
            ·
              refine ⟨1333043450362901042164529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888695633575267361443019 1333043450362901042164529)
              ·
                refine ⟨999782587772175781623397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333043450362901042164529 999782587772175781623397)
                ·
                  refine ⟨187459235207282959054387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 999782587772175781623397 187459235207282959054387)
                  ·
                    rfl

theorem cell20_410710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_410710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410710 prefixEnd_410710 := by exact prefixLift 410710
  have htrace : WordTrace (prefixWord ++ tailWord_410710) baseStart_410710 baseEnd_410710 := by
    simpa [prefixWord, tailWord_410710, baseEnd_410710] using wordTrace_append hprefix tailTrace_410710
  have hstable : (prefixWord ++ tailWord_410710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410710).length < 2 ^ (prefixWord ++ tailWord_410710).sum := by decide
  have hdescent : baseEnd_410710 < baseStart_410710 := by decide
  rcases family_descends (prefixWord ++ tailWord_410710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410711 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_410711 : Nat := 118140960795 + 410711 * 2 ^ 59
def prefixEnd_410711 : Nat := 4983230072969 + 3 ^ 40 * 410711 * 2
def baseEnd_410711 : Nat := 187459691634531400021049

theorem tailTrace_410711 : CollatzResearch.WordTrace tailWord_410711 prefixEnd_410711 187459691634531400021049 := by
  unfold tailWord_410711
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979860815071665699471987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986573876714443799647991 14979860815071665699471987)
  ·
    refine ⟨22469791222607498549207981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14979860815071665699471987 22469791222607498549207981)
    ·
      refine ⟨8426171708477811955952993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22469791222607498549207981 8426171708477811955952993)
      ·
        refine ⟨6319628781358358966964745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8426171708477811955952993 6319628781358358966964745)
        ·
          refine ⟨4739721586018769225223559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319628781358358966964745 4739721586018769225223559)
          ·
            refine ⟨7109582379028153837835339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739721586018769225223559 7109582379028153837835339)
            ·
              refine ⟨10664373568542230756753009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109582379028153837835339 10664373568542230756753009)
              ·
                refine ⟨7998280176406673067564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10664373568542230756753009 7998280176406673067564757)
                ·
                  refine ⟨187459691634531400021049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7998280176406673067564757 187459691634531400021049)
                  ·
                    rfl

theorem cell20_410711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_410711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410711 prefixEnd_410711 := by exact prefixLift 410711
  have htrace : WordTrace (prefixWord ++ tailWord_410711) baseStart_410711 baseEnd_410711 := by
    simpa [prefixWord, tailWord_410711, baseEnd_410711] using wordTrace_append hprefix tailTrace_410711
  have hstable : (prefixWord ++ tailWord_410711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410711).length < 2 ^ (prefixWord ++ tailWord_410711).sum := by decide
  have hdescent : baseEnd_410711 < baseStart_410711 := by decide
  rcases family_descends (prefixWord ++ tailWord_410711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410717 : List Nat := [1, 4, 4, 1, 2, 1, 3, 4]
def baseStart_410717 : Nat := 118140960795 + 410717 * 2 ^ 59
def prefixEnd_410717 : Nat := 4983230072969 + 3 ^ 40 * 410717 * 2
def baseEnd_410717 : Nat := 62487476732674015273675

theorem tailTrace_410717 : CollatzResearch.WordTrace tailWord_410717 prefixEnd_410717 62487476732674015273675 := by
  unfold tailWord_410717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14980079653049928724190405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986719768699952482793603 14980079653049928724190405)
  ·
    refine ⟨2808764934946861635785701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14980079653049928724190405 2808764934946861635785701)
    ·
      refine ⟨526643425302536556709819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2808764934946861635785701 526643425302536556709819)
      ·
        refine ⟨789965137953804835064729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526643425302536556709819 789965137953804835064729)
        ·
          refine ⟨592473853465353626298547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789965137953804835064729 592473853465353626298547)
          ·
            refine ⟨888710780198030439447821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592473853465353626298547 888710780198030439447821)
            ·
              refine ⟨333266542574261414792933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 888710780198030439447821 333266542574261414792933)
              ·
                refine ⟨62487476732674015273675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333266542574261414792933 62487476732674015273675)
                ·
                  rfl

theorem cell20_410717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_410717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410717 prefixEnd_410717 := by exact prefixLift 410717
  have htrace : WordTrace (prefixWord ++ tailWord_410717) baseStart_410717 baseEnd_410717 := by
    simpa [prefixWord, tailWord_410717, baseEnd_410717] using wordTrace_append hprefix tailTrace_410717
  have hstable : (prefixWord ++ tailWord_410717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410717).length < 2 ^ (prefixWord ++ tailWord_410717).sum := by decide
  have hdescent : baseEnd_410717 < baseStart_410717 := by decide
  rcases family_descends (prefixWord ++ tailWord_410717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410741 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 3]
def baseStart_410741 : Nat := 118140960795 + 410741 * 2 ^ 59
def prefixEnd_410741 : Nat := 4983230072969 + 3 ^ 40 * 410741 * 2
def baseEnd_410741 : Nat := 187473384451984629020927

theorem tailTrace_410741 : CollatzResearch.WordTrace tailWord_410741 prefixEnd_410741 187473384451984629020927 := by
  unfold tailWord_410741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14980955004962980823064077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9987303336641987215376051 14980955004962980823064077)
  ·
    refine ⟨5617858126861117808649029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14980955004962980823064077 5617858126861117808649029)
    ·
      refine ⟨1053348398786459589121693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5617858126861117808649029 1053348398786459589121693)
      ·
        refine ⟨395005649544922345920635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1053348398786459589121693 395005649544922345920635)
        ·
          refine ⟨592508474317383518880953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395005649544922345920635 592508474317383518880953)
          ·
            refine ⟨444381355738037639160715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592508474317383518880953 444381355738037639160715)
            ·
              refine ⟨666572033607056458741073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444381355738037639160715 666572033607056458741073)
              ·
                refine ⟨499929025205292344055805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666572033607056458741073 499929025205292344055805)
                ·
                  refine ⟨187473384451984629020927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499929025205292344055805 187473384451984629020927)
                  ·
                    rfl

theorem cell20_410741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_410741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410741 prefixEnd_410741 := by exact prefixLift 410741
  have htrace : WordTrace (prefixWord ++ tailWord_410741) baseStart_410741 baseEnd_410741 := by
    simpa [prefixWord, tailWord_410741, baseEnd_410741] using wordTrace_append hprefix tailTrace_410741
  have hstable : (prefixWord ++ tailWord_410741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410741).length < 2 ^ (prefixWord ++ tailWord_410741).sum := by decide
  have hdescent : baseEnd_410741 < baseStart_410741 := by decide
  rcases family_descends (prefixWord ++ tailWord_410741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410752 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 2]
def baseStart_410752 : Nat := 118140960795 + 410752 * 2 ^ 59
def prefixEnd_410752 : Nat := 4983230072969 + 3 ^ 40 * 410752 * 2
def baseEnd_410752 : Nat := 187478405151717479654215

theorem tailTrace_410752 : CollatzResearch.WordTrace tailWord_410752 prefixEnd_410752 187478405151717479654215 := by
  unfold tailWord_410752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490678103961564850857255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9987570805282086467809673 7490678103961564850857255)
  ·
    refine ⟨11236017155942347276285883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7490678103961564850857255 11236017155942347276285883)
    ·
      refine ⟨16854025733913520914428825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11236017155942347276285883 16854025733913520914428825)
      ·
        refine ⟨12640519300435140685821619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16854025733913520914428825 12640519300435140685821619)
        ·
          refine ⟨18960778950652711028732429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640519300435140685821619 18960778950652711028732429)
          ·
            refine ⟨7110292106494766635774661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18960778950652711028732429 7110292106494766635774661)
            ·
              refine ⟨1333179769967768744207749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7110292106494766635774661 1333179769967768744207749)
              ·
                refine ⟨249971206868956639538953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1333179769967768744207749 249971206868956639538953)
                ·
                  refine ⟨187478405151717479654215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249971206868956639538953 187478405151717479654215)
                  ·
                    rfl

theorem cell20_410752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_410752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410752 prefixEnd_410752 := by exact prefixLift 410752
  have htrace : WordTrace (prefixWord ++ tailWord_410752) baseStart_410752 baseEnd_410752 := by
    simpa [prefixWord, tailWord_410752, baseEnd_410752] using wordTrace_append hprefix tailTrace_410752
  have hstable : (prefixWord ++ tailWord_410752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410752).length < 2 ^ (prefixWord ++ tailWord_410752).sum := by decide
  have hdescent : baseEnd_410752 < baseStart_410752 := by decide
  rcases family_descends (prefixWord ++ tailWord_410752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410776 : List Nat := [2, 1, 2, 4, 2, 3, 2, 4]
def baseStart_410776 : Nat := 118140960795 + 410776 * 2 ^ 59
def prefixEnd_410776 : Nat := 4983230072969 + 3 ^ 40 * 410776 * 2
def baseEnd_410776 : Nat := 62496453135226687618039

theorem tailTrace_410776 : CollatzResearch.WordTrace tailWord_410776 prefixEnd_410776 62496453135226687618039 := by
  unfold tailWord_410776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7491115779918090900294091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9988154373224121200392121 7491115779918090900294091)
  ·
    refine ⟨11236673669877136350441137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7491115779918090900294091 11236673669877136350441137)
    ·
      refine ⟨8427505252407852262830853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11236673669877136350441137 8427505252407852262830853)
      ·
        refine ⟨1580157234826472299280785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8427505252407852262830853 1580157234826472299280785)
        ·
          refine ⟨1185117926119854224460589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1580157234826472299280785 1185117926119854224460589)
          ·
            refine ⟨444419222294945334172721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1185117926119854224460589 444419222294945334172721)
            ·
              refine ⟨333314416721209000629541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444419222294945334172721 333314416721209000629541)
              ·
                refine ⟨62496453135226687618039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333314416721209000629541 62496453135226687618039)
                ·
                  rfl

theorem cell20_410776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_410776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410776 prefixEnd_410776 := by exact prefixLift 410776
  have htrace : WordTrace (prefixWord ++ tailWord_410776) baseStart_410776 baseEnd_410776 := by
    simpa [prefixWord, tailWord_410776, baseEnd_410776] using wordTrace_append hprefix tailTrace_410776
  have hstable : (prefixWord ++ tailWord_410776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410776).length < 2 ^ (prefixWord ++ tailWord_410776).sum := by decide
  have hdescent : baseEnd_410776 < baseStart_410776 := by decide
  rcases family_descends (prefixWord ++ tailWord_410776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410807 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 2]
def baseStart_410807 : Nat := 118140960795 + 410807 * 2 ^ 59
def prefixEnd_410807 : Nat := 4983230072969 + 3 ^ 40 * 410807 * 2
def baseEnd_410807 : Nat := 187503508650381732820657

theorem tailTrace_410807 : CollatzResearch.WordTrace tailWord_410807 prefixEnd_410807 187503508650381732820657 := by
  unfold tailWord_410807
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983362222723874094966675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9988908148482582729977783 14983362222723874094966675)
  ·
    refine ⟨22475043334085811142450013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14983362222723874094966675 22475043334085811142450013)
    ·
      refine ⟨8428141250282179178418755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22475043334085811142450013 8428141250282179178418755)
      ·
        refine ⟨12642211875423268767628133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428141250282179178418755 12642211875423268767628133)
        ·
          refine ⟨2370414726641862893930275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12642211875423268767628133 2370414726641862893930275)
          ·
            refine ⟨3555622089962794340895413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370414726641862893930275 3555622089962794340895413)
            ·
              refine ⟨333339570934011969458945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3555622089962794340895413 333339570934011969458945)
              ·
                refine ⟨250004678200508977094209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333339570934011969458945 250004678200508977094209)
                ·
                  refine ⟨187503508650381732820657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250004678200508977094209 187503508650381732820657)
                  ·
                    rfl

theorem cell20_410807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 2].length) (baseStart_410807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410807 prefixEnd_410807 := by exact prefixLift 410807
  have htrace : WordTrace (prefixWord ++ tailWord_410807) baseStart_410807 baseEnd_410807 := by
    simpa [prefixWord, tailWord_410807, baseEnd_410807] using wordTrace_append hprefix tailTrace_410807
  have hstable : (prefixWord ++ tailWord_410807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410807).length < 2 ^ (prefixWord ++ tailWord_410807).sum := by decide
  have hdescent : baseEnd_410807 < baseStart_410807 := by decide
  rcases family_descends (prefixWord ++ tailWord_410807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410817 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 3]
def baseStart_410817 : Nat := 118140960795 + 410817 * 2 ^ 59
def prefixEnd_410817 : Nat := 4983230072969 + 3 ^ 40 * 410817 * 2
def baseEnd_410817 : Nat := 187508072922866142487283

theorem tailTrace_410817 : CollatzResearch.WordTrace tailWord_410817 prefixEnd_410817 187508072922866142487283 := by
  unfold tailWord_410817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983726952687645802830705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9989151301791763868553803 14983726952687645802830705)
  ·
    refine ⟨11237795214515734352123029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14983726952687645802830705 11237795214515734352123029)
    ·
      refine ⟨526771650680425047755767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11237795214515734352123029 526771650680425047755767)
      ·
        refine ⟨790157476020637571633651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526771650680425047755767 790157476020637571633651)
        ·
          refine ⟨1185236214030956357450477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790157476020637571633651 1185236214030956357450477)
          ·
            refine ⟨444463580261608634043929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1185236214030956357450477 444463580261608634043929)
            ·
              refine ⟨333347685196206475532947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444463580261608634043929 333347685196206475532947)
              ·
                refine ⟨500021527794309713299421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333347685196206475532947 500021527794309713299421)
                ·
                  refine ⟨187508072922866142487283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500021527794309713299421 187508072922866142487283)
                  ·
                    rfl

theorem cell20_410817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_410817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410817 prefixEnd_410817 := by exact prefixLift 410817
  have htrace : WordTrace (prefixWord ++ tailWord_410817) baseStart_410817 baseEnd_410817 := by
    simpa [prefixWord, tailWord_410817, baseEnd_410817] using wordTrace_append hprefix tailTrace_410817
  have hstable : (prefixWord ++ tailWord_410817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410817).length < 2 ^ (prefixWord ++ tailWord_410817).sum := by decide
  have hdescent : baseEnd_410817 < baseStart_410817 := by decide
  rcases family_descends (prefixWord ++ tailWord_410817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410901 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_410901 : Nat := 118140960795 + 410901 * 2 ^ 59
def prefixEnd_410901 : Nat := 4983230072969 + 3 ^ 40 * 410901 * 2
def baseEnd_410901 : Nat := 187546412811735183686939

theorem tailTrace_410901 : CollatzResearch.WordTrace tailWord_410901 prefixEnd_410901 187546412811735183686939 := by
  unfold tailWord_410901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14986790684383328148888557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9991193789588885432592371 14986790684383328148888557)
  ·
    refine ⟨5620046506643748055833209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14986790684383328148888557 5620046506643748055833209)
    ·
      refine ⟨4215034879982811041874907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5620046506643748055833209 4215034879982811041874907)
      ·
        refine ⟨6322552319974216562812361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215034879982811041874907 6322552319974216562812361)
        ·
          refine ⟨4741914239980662422109271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6322552319974216562812361 4741914239980662422109271)
          ·
            refine ⟨7112871359970993633163907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741914239980662422109271 7112871359970993633163907)
            ·
              refine ⟨10669307039956490449745861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7112871359970993633163907 10669307039956490449745861)
              ·
                refine ⟨2000495069991841959327349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10669307039956490449745861 2000495069991841959327349)
                ·
                  refine ⟨187546412811735183686939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2000495069991841959327349 187546412811735183686939)
                  ·
                    rfl

theorem cell20_410901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_410901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410901 prefixEnd_410901 := by exact prefixLift 410901
  have htrace : WordTrace (prefixWord ++ tailWord_410901) baseStart_410901 baseEnd_410901 := by
    simpa [prefixWord, tailWord_410901, baseEnd_410901] using wordTrace_append hprefix tailTrace_410901
  have hstable : (prefixWord ++ tailWord_410901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410901).length < 2 ^ (prefixWord ++ tailWord_410901).sum := by decide
  have hdescent : baseEnd_410901 < baseStart_410901 := by decide
  rcases family_descends (prefixWord ++ tailWord_410901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410904 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 2]
def baseStart_410904 : Nat := 118140960795 + 410904 * 2 ^ 59
def prefixEnd_410904 : Nat := 4983230072969 + 3 ^ 40 * 410904 * 2
def baseEnd_410904 : Nat := 187547782093480506586927

theorem tailTrace_410904 : CollatzResearch.WordTrace tailWord_410904 prefixEnd_410904 187547782093480506586927 := by
  unfold tailWord_410904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7493450051686229830623883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9991266735581639774165177 7493450051686229830623883)
  ·
    refine ⟨11240175077529344745935825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7493450051686229830623883 11240175077529344745935825)
    ·
      refine ⟨8430131308147008559451869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11240175077529344745935825 8430131308147008559451869)
      ·
        refine ⟨3161299240555128209794451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8430131308147008559451869 3161299240555128209794451)
        ·
          refine ⟨4741948860832692314691677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161299240555128209794451 4741948860832692314691677)
          ·
            refine ⟨1778230822812259618009379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4741948860832692314691677 1778230822812259618009379)
            ·
              refine ⟨2667346234218389427014069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778230822812259618009379 2667346234218389427014069)
              ·
                refine ⟨250063709457974008782569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2667346234218389427014069 250063709457974008782569)
                ·
                  refine ⟨187547782093480506586927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250063709457974008782569 187547782093480506586927)
                  ·
                    rfl

theorem cell20_410904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_410904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410904 prefixEnd_410904 := by exact prefixLift 410904
  have htrace : WordTrace (prefixWord ++ tailWord_410904) baseStart_410904 baseEnd_410904 := by
    simpa [prefixWord, tailWord_410904, baseEnd_410904] using wordTrace_append hprefix tailTrace_410904
  have hstable : (prefixWord ++ tailWord_410904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410904).length < 2 ^ (prefixWord ++ tailWord_410904).sum := by decide
  have hdescent : baseEnd_410904 < baseStart_410904 := by decide
  rcases family_descends (prefixWord ++ tailWord_410904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410910 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_410910 : Nat := 118140960795 + 410910 * 2 ^ 59
def prefixEnd_410910 : Nat := 4983230072969 + 3 ^ 40 * 410910 * 2
def baseEnd_410910 : Nat := 187550520656971152386903

theorem tailTrace_410910 : CollatzResearch.WordTrace tailWord_410910 prefixEnd_410910 187550520656971152386903 := by
  unfold tailWord_410910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873389867668840335745773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9991412627567148457310789 1873389867668840335745773)
  ·
    refine ⟨702521200375815125904665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1873389867668840335745773 702521200375815125904665)
    ·
      refine ⟨526890900281861344428499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702521200375815125904665 526890900281861344428499)
      ·
        refine ⟨790336350422792016642749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526890900281861344428499 790336350422792016642749)
        ·
          refine ⟨296376131408547006241031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 790336350422792016642749 296376131408547006241031)
          ·
            refine ⟨444564197112820509361547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296376131408547006241031 444564197112820509361547)
            ·
              refine ⟨666846295669230764042321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444564197112820509361547 666846295669230764042321)
              ·
                refine ⟨500134721751923073031741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666846295669230764042321 500134721751923073031741)
                ·
                  refine ⟨187550520656971152386903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500134721751923073031741 187550520656971152386903)
                  ·
                    rfl

theorem cell20_410910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_410910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410910 prefixEnd_410910 := by exact prefixLift 410910
  have htrace : WordTrace (prefixWord ++ tailWord_410910) baseStart_410910 baseEnd_410910 := by
    simpa [prefixWord, tailWord_410910, baseEnd_410910] using wordTrace_append hprefix tailTrace_410910
  have hstable : (prefixWord ++ tailWord_410910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410910).length < 2 ^ (prefixWord ++ tailWord_410910).sum := by decide
  have hdescent : baseEnd_410910 < baseStart_410910 := by decide
  rcases family_descends (prefixWord ++ tailWord_410910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410914 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_410914 : Nat := 118140960795 + 410914 * 2 ^ 59
def prefixEnd_410914 : Nat := 4983230072969 + 3 ^ 40 * 410914 * 2
def baseEnd_410914 : Nat := 187552346365964916253553

theorem tailTrace_410914 : CollatzResearch.WordTrace tailWord_410914 prefixEnd_410914 187552346365964916253553 := by
  unfold tailWord_410914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3746816208334057842277949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9991509888890820912741197 3746816208334057842277949)
  ·
    refine ⟨1405056078125271690854231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3746816208334057842277949 1405056078125271690854231)
    ·
      refine ⟨2107584117187907536281347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405056078125271690854231 2107584117187907536281347)
      ·
        refine ⟨3161376175781861304422021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107584117187907536281347 3161376175781861304422021)
        ·
          refine ⟨592758032959098994579129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3161376175781861304422021 592758032959098994579129)
          ·
            refine ⟨444568524719324245934347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592758032959098994579129 444568524719324245934347)
            ·
              refine ⟨666852787078986368901521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444568524719324245934347 666852787078986368901521)
              ·
                refine ⟨500139590309239776676141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666852787078986368901521 500139590309239776676141)
                ·
                  refine ⟨187552346365964916253553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500139590309239776676141 187552346365964916253553)
                  ·
                    rfl

theorem cell20_410914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_410914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410914 prefixEnd_410914 := by exact prefixLift 410914
  have htrace : WordTrace (prefixWord ++ tailWord_410914) baseStart_410914 baseEnd_410914 := by
    simpa [prefixWord, tailWord_410914, baseEnd_410914] using wordTrace_append hprefix tailTrace_410914
  have hstable : (prefixWord ++ tailWord_410914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410914).length < 2 ^ (prefixWord ++ tailWord_410914).sum := by decide
  have hdescent : baseEnd_410914 < baseStart_410914 := by decide
  rcases family_descends (prefixWord ++ tailWord_410914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410980 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 4]
def baseStart_410980 : Nat := 118140960795 + 410980 * 2 ^ 59
def prefixEnd_410980 : Nat := 4983230072969 + 3 ^ 40 * 410980 * 2
def baseEnd_410980 : Nat := 187582470564362020053283

theorem tailTrace_410980 : CollatzResearch.WordTrace tailWord_410980 prefixEnd_410980 187582470564362020053283 := by
  unfold tailWord_410980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7494836025548562320507197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9993114700731416427342929 7494836025548562320507197)
  ·
    refine ⟨2810563509580710870190199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7494836025548562320507197 2810563509580710870190199)
    ·
      refine ⟨4215845264371066305285299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810563509580710870190199 4215845264371066305285299)
      ·
        refine ⟨6323767896556599457927949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215845264371066305285299 6323767896556599457927949)
        ·
          refine ⟨2371412961208724796722981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6323767896556599457927949 2371412961208724796722981)
          ·
            refine ⟨444639930226635899385559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2371412961208724796722981 444639930226635899385559)
            ·
              refine ⟨666959895339953849078339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444639930226635899385559 666959895339953849078339)
              ·
                refine ⟨1000439843009930773617509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666959895339953849078339 1000439843009930773617509)
                ·
                  refine ⟨187582470564362020053283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000439843009930773617509 187582470564362020053283)
                  ·
                    rfl

theorem cell20_410980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_410980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410980 prefixEnd_410980 := by exact prefixLift 410980
  have htrace : WordTrace (prefixWord ++ tailWord_410980) baseStart_410980 baseEnd_410980 := by
    simpa [prefixWord, tailWord_410980, baseEnd_410980] using wordTrace_append hprefix tailTrace_410980
  have hstable : (prefixWord ++ tailWord_410980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410980).length < 2 ^ (prefixWord ++ tailWord_410980).sum := by decide
  have hdescent : baseEnd_410980 < baseStart_410980 := by decide
  rcases family_descends (prefixWord ++ tailWord_410980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410990 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_410990 : Nat := 118140960795 + 410990 * 2 ^ 59
def prefixEnd_410990 : Nat := 4983230072969 + 3 ^ 40 * 410990 * 2
def baseEnd_410990 : Nat := 187587034836846429719909

theorem tailTrace_410990 : CollatzResearch.WordTrace tailWord_410990 prefixEnd_410990 187587034836846429719909 := by
  unfold tailWord_410990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873754597632612043609803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9993357854040597565918949 1873754597632612043609803)
  ·
    refine ⟨2810631896448918065414705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873754597632612043609803 2810631896448918065414705)
    ·
      refine ⟨2107973922336688549061029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2810631896448918065414705 2107973922336688549061029)
      ·
        refine ⟨395245110438129102948943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2107973922336688549061029 395245110438129102948943)
        ·
          refine ⟨592867665657193654423415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395245110438129102948943 592867665657193654423415)
          ·
            refine ⟨889301498485790481635123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592867665657193654423415 889301498485790481635123)
            ·
              refine ⟨1333952247728685722452685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889301498485790481635123 1333952247728685722452685)
              ·
                refine ⟨500232092898257145919757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333952247728685722452685 500232092898257145919757)
                ·
                  refine ⟨187587034836846429719909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500232092898257145919757 187587034836846429719909)
                  ·
                    rfl

theorem cell20_410990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_410990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410990 prefixEnd_410990 := by exact prefixLift 410990
  have htrace : WordTrace (prefixWord ++ tailWord_410990) baseStart_410990 baseEnd_410990 := by
    simpa [prefixWord, tailWord_410990, baseEnd_410990] using wordTrace_append hprefix tailTrace_410990
  have hstable : (prefixWord ++ tailWord_410990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410990).length < 2 ^ (prefixWord ++ tailWord_410990).sum := by decide
  have hdescent : baseEnd_410990 < baseStart_410990 := by decide
  rcases family_descends (prefixWord ++ tailWord_410990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410994 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_410994 : Nat := 118140960795 + 410994 * 2 ^ 59
def prefixEnd_410994 : Nat := 4983230072969 + 3 ^ 40 * 410994 * 2
def baseEnd_410994 : Nat := 187588860545840193586559

theorem tailTrace_410994 : CollatzResearch.WordTrace tailWord_410994 prefixEnd_410994 187588860545840193586559 := by
  unfold tailWord_410994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747545668261601258006009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9993455115364270021349357 3747545668261601258006009)
  ·
    refine ⟨2810659251196200943504507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3747545668261601258006009 2810659251196200943504507)
    ·
      refine ⟨4215988876794301415256761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810659251196200943504507 4215988876794301415256761)
      ·
        refine ⟨3161991657595726061442571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4215988876794301415256761 3161991657595726061442571)
        ·
          refine ⟨4742987486393589092163857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161991657595726061442571 4742987486393589092163857)
          ·
            refine ⟨3557240614795191819122893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4742987486393589092163857 3557240614795191819122893)
            ·
              refine ⟨1333965230548196932171085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3557240614795191819122893 1333965230548196932171085)
              ·
                refine ⟨500236961455573849564157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333965230548196932171085 500236961455573849564157)
                ·
                  refine ⟨187588860545840193586559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500236961455573849564157 187588860545840193586559)
                  ·
                    rfl

theorem cell20_410994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_410994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_410994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_410994 prefixEnd_410994 := by exact prefixLift 410994
  have htrace : WordTrace (prefixWord ++ tailWord_410994) baseStart_410994 baseEnd_410994 := by
    simpa [prefixWord, tailWord_410994, baseEnd_410994] using wordTrace_append hprefix tailTrace_410994
  have hstable : (prefixWord ++ tailWord_410994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410994).length < 2 ^ (prefixWord ++ tailWord_410994).sum := by decide
  have hdescent : baseEnd_410994 < baseStart_410994 := by decide
  rcases family_descends (prefixWord ++ tailWord_410994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411084 : List Nat := [2, 2, 1, 4, 2, 2, 7]
def baseStart_411084 : Nat := 118140960795 + 411084 * 2 ^ 59
def prefixEnd_411084 : Nat := 4983230072969 + 3 ^ 40 * 411084 * 2
def baseEnd_411084 : Nat := 20847770999799986731799

theorem tailTrace_411084 : CollatzResearch.WordTrace tailWord_411084 prefixEnd_411084 20847770999799986731799 := by
  unfold tailWord_411084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7496732621360175201400153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9995643495146900268533537 7496732621360175201400153)
  ·
    refine ⟨5622549466020131401050115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7496732621360175201400153 5622549466020131401050115)
    ·
      refine ⟨8433824199030197101575173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5622549466020131401050115 8433824199030197101575173)
      ·
        refine ⟨1581342037318161956545345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8433824199030197101575173 1581342037318161956545345)
        ·
          refine ⟨1186006527988621467409009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581342037318161956545345 1186006527988621467409009)
          ·
            refine ⟨889504895991466100556757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186006527988621467409009 889504895991466100556757)
            ·
              refine ⟨20847770999799986731799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 889504895991466100556757 20847770999799986731799)
              ·
                rfl

theorem cell20_411084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 7].length) (baseStart_411084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411084 prefixEnd_411084 := by exact prefixLift 411084
  have htrace : WordTrace (prefixWord ++ tailWord_411084) baseStart_411084 baseEnd_411084 := by
    simpa [prefixWord, tailWord_411084, baseEnd_411084] using wordTrace_append hprefix tailTrace_411084
  have hstable : (prefixWord ++ tailWord_411084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411084).length < 2 ^ (prefixWord ++ tailWord_411084).sum := by decide
  have hdescent : baseEnd_411084 < baseStart_411084 := by decide
  rcases family_descends (prefixWord ++ tailWord_411084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411094 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_411094 : Nat := 118140960795 + 411094 * 2 ^ 59
def prefixEnd_411094 : Nat := 4983230072969 + 3 ^ 40 * 411094 * 2
def baseEnd_411094 : Nat := 187634503270684290252817

theorem tailTrace_411094 : CollatzResearch.WordTrace tailWord_411094 prefixEnd_411094 187634503270684290252817 := by
  unfold tailWord_411094
  simp only [CollatzResearch.WordTrace]
  refine ⟨937114373292757631916521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9995886648456081407109557 937114373292757631916521)
  ·
    refine ⟨702835779969568223937391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 937114373292757631916521 702835779969568223937391)
    ·
      refine ⟨1054253669954352335906087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 702835779969568223937391 1054253669954352335906087)
      ·
        refine ⟨1581380504931528503859131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054253669954352335906087 1581380504931528503859131)
        ·
          refine ⟨2372070757397292755788697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581380504931528503859131 2372070757397292755788697)
          ·
            refine ⟨1779053068047969566841523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2372070757397292755788697 1779053068047969566841523)
            ·
              refine ⟨2668579602071954350262285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779053068047969566841523 2668579602071954350262285)
              ·
                refine ⟨1000717350776982881348357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2668579602071954350262285 1000717350776982881348357)
                ·
                  refine ⟨187634503270684290252817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000717350776982881348357 187634503270684290252817)
                  ·
                    rfl

theorem cell20_411094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_411094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411094 prefixEnd_411094 := by exact prefixLift 411094
  have htrace : WordTrace (prefixWord ++ tailWord_411094) baseStart_411094 baseEnd_411094 := by
    simpa [prefixWord, tailWord_411094, baseEnd_411094] using wordTrace_append hprefix tailTrace_411094
  have hstable : (prefixWord ++ tailWord_411094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411094).length < 2 ^ (prefixWord ++ tailWord_411094).sum := by decide
  have hdescent : baseEnd_411094 < baseStart_411094 := by decide
  rcases family_descends (prefixWord ++ tailWord_411094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411132 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 2]
def baseStart_411132 : Nat := 118140960795 + 411132 * 2 ^ 59
def prefixEnd_411132 : Nat := 4983230072969 + 3 ^ 40 * 411132 * 2
def baseEnd_411132 : Nat := 187651847506125046985995

theorem tailTrace_411132 : CollatzResearch.WordTrace tailWord_411132 prefixEnd_411132 187651847506125046985995 := by
  unfold tailWord_411132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497607973273227300273825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9996810631030969733698433 7497607973273227300273825)
  ·
    refine ⟨5623205979954920475205369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7497607973273227300273825 5623205979954920475205369)
    ·
      refine ⟨4217404484966190356404027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5623205979954920475205369 4217404484966190356404027)
      ·
        refine ⟨6326106727449285534606041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4217404484966190356404027 6326106727449285534606041)
        ·
          refine ⟨4744580045586964150954531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6326106727449285534606041 4744580045586964150954531)
          ·
            refine ⟨7116870068380446226431797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4744580045586964150954531 7116870068380446226431797)
            ·
              refine ⟨667206568910666833727981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7116870068380446226431797 667206568910666833727981)
              ·
                refine ⟨250202463341500062647993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 667206568910666833727981 250202463341500062647993)
                ·
                  refine ⟨187651847506125046985995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250202463341500062647993 187651847506125046985995)
                  ·
                    rfl

theorem cell20_411132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_411132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411132 prefixEnd_411132 := by exact prefixLift 411132
  have htrace : WordTrace (prefixWord ++ tailWord_411132) baseStart_411132 baseEnd_411132 := by
    simpa [prefixWord, tailWord_411132, baseEnd_411132] using wordTrace_append hprefix tailTrace_411132
  have hstable : (prefixWord ++ tailWord_411132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411132).length < 2 ^ (prefixWord ++ tailWord_411132).sum := by decide
  have hdescent : baseEnd_411132 < baseStart_411132 := by decide
  rcases family_descends (prefixWord ++ tailWord_411132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411156 : List Nat := [2, 4, 3, 1, 2, 1, 2, 5]
def baseStart_411156 : Nat := 118140960795 + 411156 * 2 ^ 59
def prefixEnd_411156 : Nat := 4983230072969 + 3 ^ 40 * 411156 * 2
def baseEnd_411156 : Nat := 62554267253362543395299

theorem tailTrace_411156 : CollatzResearch.WordTrace tailWord_411156 prefixEnd_411156 62554267253362543395299 := by
  unfold tailWord_411156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7498045649229753349710661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9997394198973004466280881 7498045649229753349710661)
  ·
    refine ⟨1405883559230578753070749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7498045649229753349710661 1405883559230578753070749)
    ·
      refine ⟨527206334711467032401531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1405883559230578753070749 527206334711467032401531)
      ·
        refine ⟨790809502067200548602297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527206334711467032401531 790809502067200548602297)
        ·
          refine ⟨593107126550400411451723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790809502067200548602297 593107126550400411451723)
          ·
            refine ⟨889660689825600617177585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593107126550400411451723 889660689825600617177585)
            ·
              refine ⟨667245517369200462883189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889660689825600617177585 667245517369200462883189)
              ·
                refine ⟨62554267253362543395299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 667245517369200462883189 62554267253362543395299)
                ·
                  rfl

theorem cell20_411156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_411156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411156 prefixEnd_411156 := by exact prefixLift 411156
  have htrace : WordTrace (prefixWord ++ tailWord_411156) baseStart_411156 baseEnd_411156 := by
    simpa [prefixWord, tailWord_411156, baseEnd_411156] using wordTrace_append hprefix tailTrace_411156
  have hstable : (prefixWord ++ tailWord_411156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411156).length < 2 ^ (prefixWord ++ tailWord_411156).sum := by decide
  have hdescent : baseEnd_411156 < baseStart_411156 := by decide
  rcases family_descends (prefixWord ++ tailWord_411156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411257 : List Nat := [1, 2, 1, 3, 3, 1, 9]
def baseStart_411257 : Nat := 118140960795 + 411257 * 2 ^ 59
def prefixEnd_411257 : Nat := 4983230072969 + 3 ^ 40 * 411257 * 2
def baseEnd_411257 : Nat := 20856544545797796424313

theorem tailTrace_411257 : CollatzResearch.WordTrace tailWord_411257 prefixEnd_411257 20856544545797796424313 := by
  unfold tailWord_411257
  simp only [CollatzResearch.WordTrace]
  refine ⟨14999775071093600948848025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9999850047395733965898683 14999775071093600948848025)
  ·
    refine ⟨11249831303320200711636019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14999775071093600948848025 11249831303320200711636019)
    ·
      refine ⟨16874746954980301067454029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11249831303320200711636019 16874746954980301067454029)
      ·
        refine ⟨6328030108117612900295261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16874746954980301067454029 6328030108117612900295261)
        ·
          refine ⟨2373011290544104837610723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6328030108117612900295261 2373011290544104837610723)
          ·
            refine ⟨3559516935816157256416085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373011290544104837610723 3559516935816157256416085)
            ·
              refine ⟨20856544545797796424313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3559516935816157256416085 20856544545797796424313)
              ·
                rfl

theorem cell20_411257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_411257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411257 prefixEnd_411257 := by exact prefixLift 411257
  have htrace : WordTrace (prefixWord ++ tailWord_411257) baseStart_411257 baseEnd_411257 := by
    simpa [prefixWord, tailWord_411257, baseEnd_411257] using wordTrace_append hprefix tailTrace_411257
  have hstable : (prefixWord ++ tailWord_411257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411257).length < 2 ^ (prefixWord ++ tailWord_411257).sum := by decide
  have hdescent : baseEnd_411257 < baseStart_411257 := by decide
  rcases family_descends (prefixWord ++ tailWord_411257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411319 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_411319 : Nat := 118140960795 + 411319 * 2 ^ 59
def prefixEnd_411319 : Nat := 4983230072969 + 3 ^ 40 * 411319 * 2
def baseEnd_411319 : Nat := 187737199401583507751897

theorem tailTrace_411319 : CollatzResearch.WordTrace tailWord_411319 prefixEnd_411319 187737199401583507751897 := by
  unfold tailWord_411319
  simp only [CollatzResearch.WordTrace]
  refine ⟨15002036396868985537605011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10001357597912657025070007 15002036396868985537605011)
  ·
    refine ⟨22503054595303478306407517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15002036396868985537605011 22503054595303478306407517)
    ·
      refine ⟨8438645473238804364902819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22503054595303478306407517 8438645473238804364902819)
      ·
        refine ⟨12657968209858206547354229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8438645473238804364902819 12657968209858206547354229)
        ·
          refine ⟨1186684519674206863814459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12657968209858206547354229 1186684519674206863814459)
          ·
            refine ⟨1780026779511310295721689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186684519674206863814459 1780026779511310295721689)
            ·
              refine ⟨1335020084633482721791267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780026779511310295721689 1335020084633482721791267)
              ·
                refine ⟨2002530126950224082686901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335020084633482721791267 2002530126950224082686901)
                ·
                  refine ⟨187737199401583507751897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2002530126950224082686901 187737199401583507751897)
                  ·
                    rfl

theorem cell20_411319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_411319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411319 prefixEnd_411319 := by exact prefixLift 411319
  have htrace : WordTrace (prefixWord ++ tailWord_411319) baseStart_411319 baseEnd_411319 := by
    simpa [prefixWord, tailWord_411319, baseEnd_411319] using wordTrace_append hprefix tailTrace_411319
  have hstable : (prefixWord ++ tailWord_411319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411319).length < 2 ^ (prefixWord ++ tailWord_411319).sum := by decide
  have hdescent : baseEnd_411319 < baseStart_411319 := by decide
  rcases family_descends (prefixWord ++ tailWord_411319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411367 : List Nat := [1, 1, 5, 4, 2, 7]
def baseStart_411367 : Nat := 118140960795 + 411367 * 2 ^ 59
def prefixEnd_411367 : Nat := 4983230072969 + 3 ^ 40 * 411367 * 2
def baseEnd_411367 : Nat := 6954041033685506450063

theorem tailTrace_411367 : CollatzResearch.WordTrace tailWord_411367 prefixEnd_411367 6954041033685506450063 := by
  unfold tailWord_411367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15003787100695089735352355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10002524733796726490234903 15003787100695089735352355)
  ·
    refine ⟨22505680651042634603028533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15003787100695089735352355 22505680651042634603028533)
    ·
      refine ⟨2109907561035246994033925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22505680651042634603028533 2109907561035246994033925)
      ·
        refine ⟨395607667694108811381361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2109907561035246994033925 395607667694108811381361)
        ·
          refine ⟨296705750770581608536021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395607667694108811381361 296705750770581608536021)
          ·
            refine ⟨6954041033685506450063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 296705750770581608536021 6954041033685506450063)
            ·
              rfl

theorem cell20_411367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 7].length) (baseStart_411367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411367 prefixEnd_411367 := by exact prefixLift 411367
  have htrace : WordTrace (prefixWord ++ tailWord_411367) baseStart_411367 baseEnd_411367 := by
    simpa [prefixWord, tailWord_411367, baseEnd_411367] using wordTrace_append hprefix tailTrace_411367
  have hstable : (prefixWord ++ tailWord_411367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411367).length < 2 ^ (prefixWord ++ tailWord_411367).sum := by decide
  have hdescent : baseEnd_411367 < baseStart_411367 := by decide
  rcases family_descends (prefixWord ++ tailWord_411367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411374 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_411374 : Nat := 118140960795 + 411374 * 2 ^ 59
def prefixEnd_411374 : Nat := 4983230072969 + 3 ^ 40 * 411374 * 2
def baseEnd_411374 : Nat := 187762302900247760918339

theorem tailTrace_411374 : CollatzResearch.WordTrace tailWord_411374 prefixEnd_411374 187762302900247760918339 := by
  unfold tailWord_411374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875505301458716241357147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10002694941113153287238117 1875505301458716241357147)
  ·
    refine ⟨2813257952188074362035721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1875505301458716241357147 2813257952188074362035721)
    ·
      refine ⟨2109943464141055771526791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2813257952188074362035721 2109943464141055771526791)
      ·
        refine ⟨3164915196211583657290187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109943464141055771526791 3164915196211583657290187)
        ·
          refine ⟨4747372794317375485935281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164915196211583657290187 4747372794317375485935281)
          ·
            refine ⟨3560529595738031614451461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4747372794317375485935281 3560529595738031614451461)
            ·
              refine ⟨667599299200880927709649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3560529595738031614451461 667599299200880927709649)
              ·
                refine ⟨500699474400660695782237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667599299200880927709649 500699474400660695782237)
                ·
                  refine ⟨187762302900247760918339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500699474400660695782237 187762302900247760918339)
                  ·
                    rfl

theorem cell20_411374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_411374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411374 prefixEnd_411374 := by exact prefixLift 411374
  have htrace : WordTrace (prefixWord ++ tailWord_411374) baseStart_411374 baseEnd_411374 := by
    simpa [prefixWord, tailWord_411374, baseEnd_411374] using wordTrace_append hprefix tailTrace_411374
  have hstable : (prefixWord ++ tailWord_411374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411374).length < 2 ^ (prefixWord ++ tailWord_411374).sum := by decide
  have hdescent : baseEnd_411374 < baseStart_411374 := by decide
  rcases family_descends (prefixWord ++ tailWord_411374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411377 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 2]
def baseStart_411377 : Nat := 118140960795 + 411377 * 2 ^ 59
def prefixEnd_411377 : Nat := 4983230072969 + 3 ^ 40 * 411377 * 2
def baseEnd_411377 : Nat := 187763672181993083818327

theorem tailTrace_411377 : CollatzResearch.WordTrace tailWord_411377 prefixEnd_411377 187763672181993083818327 := by
  unfold tailWord_411377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004151830658861443216385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10002767887105907628810923 15004151830658861443216385)
  ·
    refine ⟨11253113872994146082412289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15004151830658861443216385 11253113872994146082412289)
    ·
      refine ⟨8439835404745609561809217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11253113872994146082412289 8439835404745609561809217)
      ·
        refine ⟨6329876553559207171356913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8439835404745609561809217 6329876553559207171356913)
        ·
          refine ⟨4747407415169405378517685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6329876553559207171356913 4747407415169405378517685)
          ·
            refine ⟨445069445172131754236033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4747407415169405378517685 445069445172131754236033)
            ·
              refine ⟨333802083879098815677025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445069445172131754236033 333802083879098815677025)
              ·
                refine ⟨250351562909324111757769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333802083879098815677025 250351562909324111757769)
                ·
                  refine ⟨187763672181993083818327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250351562909324111757769 187763672181993083818327)
                  ·
                    rfl

theorem cell20_411377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_411377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411377 prefixEnd_411377 := by exact prefixLift 411377
  have htrace : WordTrace (prefixWord ++ tailWord_411377) baseStart_411377 baseEnd_411377 := by
    simpa [prefixWord, tailWord_411377, baseEnd_411377] using wordTrace_append hprefix tailTrace_411377
  have hstable : (prefixWord ++ tailWord_411377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411377).length < 2 ^ (prefixWord ++ tailWord_411377).sum := by decide
  have hdescent : baseEnd_411377 < baseStart_411377 := by decide
  rcases family_descends (prefixWord ++ tailWord_411377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411395 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_411395 : Nat := 118140960795 + 411395 * 2 ^ 59
def prefixEnd_411395 : Nat := 4983230072969 + 3 ^ 40 * 411395 * 2
def baseEnd_411395 : Nat := 187771887872465021218253

theorem tailTrace_411395 : CollatzResearch.WordTrace tailWord_411395 prefixEnd_411395 187771887872465021218253 := by
  unfold tailWord_411395
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004808344593650517371639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10003205563062433678247759 15004808344593650517371639)
  ·
    refine ⟨22507212516890475776057459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004808344593650517371639 22507212516890475776057459)
    ·
      refine ⟨33760818775335713664086189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22507212516890475776057459 33760818775335713664086189)
      ·
        refine ⟨12660307040750892624032321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33760818775335713664086189 12660307040750892624032321)
        ·
          refine ⟨9495230280563169468024241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12660307040750892624032321 9495230280563169468024241)
          ·
            refine ⟨7121422710422377101018181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9495230280563169468024241 7121422710422377101018181)
            ·
              refine ⟨1335266758204195706440909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7121422710422377101018181 1335266758204195706440909)
              ·
                refine ⟨500725034326573389915341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335266758204195706440909 500725034326573389915341)
                ·
                  refine ⟨187771887872465021218253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500725034326573389915341 187771887872465021218253)
                  ·
                    rfl

theorem cell20_411395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_411395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411395 prefixEnd_411395 := by exact prefixLift 411395
  have htrace : WordTrace (prefixWord ++ tailWord_411395) baseStart_411395 baseEnd_411395 := by
    simpa [prefixWord, tailWord_411395, baseEnd_411395] using wordTrace_append hprefix tailTrace_411395
  have hstable : (prefixWord ++ tailWord_411395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411395).length < 2 ^ (prefixWord ++ tailWord_411395).sum := by decide
  have hdescent : baseEnd_411395 < baseStart_411395 := by decide
  rcases family_descends (prefixWord ++ tailWord_411395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411402 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_411402 : Nat := 118140960795 + 411402 * 2 ^ 59
def prefixEnd_411402 : Nat := 4983230072969 + 3 ^ 40 * 411402 * 2
def baseEnd_411402 : Nat := 187775082863204107984891

theorem tailTrace_411402 : CollatzResearch.WordTrace tailWord_411402 prefixEnd_411402 187775082863204107984891 := by
  unfold tailWord_411402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751265913892072678219115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10003375770378860475250973 3751265913892072678219115)
  ·
    refine ⟨5626898870838109017328673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3751265913892072678219115 5626898870838109017328673)
    ·
      refine ⟨4220174153128581762996505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5626898870838109017328673 4220174153128581762996505)
      ·
        refine ⟨3165130614846436322247379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4220174153128581762996505 3165130614846436322247379)
        ·
          refine ⟨4747695922269654483371069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165130614846436322247379 4747695922269654483371069)
          ·
            refine ⟨1780385970851120431264151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4747695922269654483371069 1780385970851120431264151)
            ·
              refine ⟨2670578956276680646896227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780385970851120431264151 2670578956276680646896227)
              ·
                refine ⟨4005868434415020970344341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2670578956276680646896227 4005868434415020970344341)
                ·
                  refine ⟨187775082863204107984891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4005868434415020970344341 187775082863204107984891)
                  ·
                    rfl

theorem cell20_411402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_411402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411402 prefixEnd_411402 := by exact prefixLift 411402
  have htrace : WordTrace (prefixWord ++ tailWord_411402) baseStart_411402 baseEnd_411402 := by
    simpa [prefixWord, tailWord_411402, baseEnd_411402] using wordTrace_append hprefix tailTrace_411402
  have hstable : (prefixWord ++ tailWord_411402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411402).length < 2 ^ (prefixWord ++ tailWord_411402).sum := by decide
  have hdescent : baseEnd_411402 < baseStart_411402 := by decide
  rcases family_descends (prefixWord ++ tailWord_411402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411422 : List Nat := [4, 3, 2, 2, 1, 1, 7]
def baseStart_411422 : Nat := 118140960795 + 411422 * 2 ^ 59
def prefixEnd_411422 : Nat := 4983230072969 + 3 ^ 40 * 411422 * 2
def baseEnd_411422 : Nat := 20864912378685880813127

theorem tailTrace_411422 : CollatzResearch.WordTrace tailWord_411422 prefixEnd_411422 20864912378685880813127 := by
  unfold tailWord_411422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875724139436979266075565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10003862076997222752403013 1875724139436979266075565)
  ·
    refine ⟨703396552288867224778337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1875724139436979266075565 703396552288867224778337)
    ·
      refine ⟨527547414216650418583753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 703396552288867224778337 527547414216650418583753)
      ·
        refine ⟨395660560662487813937815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527547414216650418583753 395660560662487813937815)
        ·
          refine ⟨593490840993731720906723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395660560662487813937815 593490840993731720906723)
          ·
            refine ⟨890236261490597581360085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593490840993731720906723 890236261490597581360085)
            ·
              refine ⟨20864912378685880813127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 890236261490597581360085 20864912378685880813127)
              ·
                rfl

theorem cell20_411422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 7].length) (baseStart_411422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411422 prefixEnd_411422 := by exact prefixLift 411422
  have htrace : WordTrace (prefixWord ++ tailWord_411422) baseStart_411422 baseEnd_411422 := by
    simpa [prefixWord, tailWord_411422, baseEnd_411422] using wordTrace_append hprefix tailTrace_411422
  have hstable : (prefixWord ++ tailWord_411422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411422).length < 2 ^ (prefixWord ++ tailWord_411422).sum := by decide
  have hdescent : baseEnd_411422 < baseStart_411422 := by decide
  rcases family_descends (prefixWord ++ tailWord_411422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411446 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_411446 : Nat := 118140960795 + 411446 * 2 ^ 59
def prefixEnd_411446 : Nat := 4983230072969 + 3 ^ 40 * 411446 * 2
def baseEnd_411446 : Nat := 187795165662135510518045

theorem tailTrace_411446 : CollatzResearch.WordTrace tailWord_411446 prefixEnd_411446 187795165662135510518045 := by
  unfold tailWord_411446
  simp only [CollatzResearch.WordTrace]
  refine ⟨937916779213055389217387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10004445644939257484985461 937916779213055389217387)
  ·
    refine ⟨1406875168819583083826081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937916779213055389217387 1406875168819583083826081)
    ·
      refine ⟨1055156376614687312869561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1406875168819583083826081 1055156376614687312869561)
      ·
        refine ⟨791367282461015484652171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055156376614687312869561 791367282461015484652171)
        ·
          refine ⟨1187050923691523226978257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791367282461015484652171 1187050923691523226978257)
          ·
            refine ⟨890288192768642420233693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187050923691523226978257 890288192768642420233693)
            ·
              refine ⟨333858072288240907587635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 890288192768642420233693 333858072288240907587635)
              ·
                refine ⟨500787108432361361381453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333858072288240907587635 500787108432361361381453)
                ·
                  refine ⟨187795165662135510518045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500787108432361361381453 187795165662135510518045)
                  ·
                    rfl

theorem cell20_411446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_411446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411446 prefixEnd_411446 := by exact prefixLift 411446
  have htrace : WordTrace (prefixWord ++ tailWord_411446) baseStart_411446 baseEnd_411446 := by
    simpa [prefixWord, tailWord_411446, baseEnd_411446] using wordTrace_append hprefix tailTrace_411446
  have hstable : (prefixWord ++ tailWord_411446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411446).length < 2 ^ (prefixWord ++ tailWord_411446).sum := by decide
  have hdescent : baseEnd_411446 < baseStart_411446 := by decide
  rcases family_descends (prefixWord ++ tailWord_411446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411464 : List Nat := [2, 1, 3, 1, 1, 4, 4, 4]
def baseStart_411464 : Nat := 118140960795 + 411464 * 2 ^ 59
def prefixEnd_411464 : Nat := 4983230072969 + 3 ^ 40 * 411464 * 2
def baseEnd_411464 : Nat := 62601127117535815972657

theorem tailTrace_411464 : CollatzResearch.WordTrace tailWord_411464 prefixEnd_411464 62601127117535815972657 := by
  unfold tailWord_411464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503662490671837650816723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10004883320895783534422297 7503662490671837650816723)
  ·
    refine ⟨11255493736007756476225085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7503662490671837650816723 11255493736007756476225085)
    ·
      refine ⟨4220810151002908678584407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11255493736007756476225085 4220810151002908678584407)
      ·
        refine ⟨6331215226504363017876611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4220810151002908678584407 6331215226504363017876611)
        ·
          refine ⟨9496822839756544526814917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6331215226504363017876611 9496822839756544526814917)
          ·
            refine ⟨1780654282454352098777797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9496822839756544526814917 1780654282454352098777797)
            ·
              refine ⟨333872677960191018520837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1780654282454352098777797 333872677960191018520837)
              ·
                refine ⟨62601127117535815972657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333872677960191018520837 62601127117535815972657)
                ·
                  rfl

theorem cell20_411464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_411464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411464 prefixEnd_411464 := by exact prefixLift 411464
  have htrace : WordTrace (prefixWord ++ tailWord_411464) baseStart_411464 baseEnd_411464 := by
    simpa [prefixWord, tailWord_411464, baseEnd_411464] using wordTrace_append hprefix tailTrace_411464
  have hstable : (prefixWord ++ tailWord_411464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411464).length < 2 ^ (prefixWord ++ tailWord_411464).sum := by decide
  have hdescent : baseEnd_411464 < baseStart_411464 := by decide
  rcases family_descends (prefixWord ++ tailWord_411464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411474 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_411474 : Nat := 118140960795 + 411474 * 2 ^ 59
def prefixEnd_411474 : Nat := 4983230072969 + 3 ^ 40 * 411474 * 2
def baseEnd_411474 : Nat := 187807945625091857584597

theorem tailTrace_411474 : CollatzResearch.WordTrace tailWord_411474 prefixEnd_411474 187807945625091857584597 := by
  unfold tailWord_411474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751922427826861752374369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10005126474204964672998317 3751922427826861752374369)
  ·
    refine ⟨2813941820870146314280777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3751922427826861752374369 2813941820870146314280777)
    ·
      refine ⟨2110456365652609735710583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2813941820870146314280777 2110456365652609735710583)
      ·
        refine ⟨3165684548478914603565875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110456365652609735710583 3165684548478914603565875)
        ·
          refine ⟨4748526822718371905348813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165684548478914603565875 4748526822718371905348813)
          ·
            refine ⟨1780697558519389464505805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4748526822718371905348813 1780697558519389464505805)
            ·
              refine ⟨667761584444771049189677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780697558519389464505805 667761584444771049189677)
              ·
                refine ⟨250410594166789143446129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 667761584444771049189677 250410594166789143446129)
                ·
                  refine ⟨187807945625091857584597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250410594166789143446129 187807945625091857584597)
                  ·
                    rfl

theorem cell20_411474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_411474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411474 prefixEnd_411474 := by exact prefixLift 411474
  have htrace : WordTrace (prefixWord ++ tailWord_411474) baseStart_411474 baseEnd_411474 := by
    simpa [prefixWord, tailWord_411474, baseEnd_411474] using wordTrace_append hprefix tailTrace_411474
  have hstable : (prefixWord ++ tailWord_411474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411474).length < 2 ^ (prefixWord ++ tailWord_411474).sum := by decide
  have hdescent : baseEnd_411474 < baseStart_411474 := by decide
  rcases family_descends (prefixWord ++ tailWord_411474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411491 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 2]
def baseStart_411491 : Nat := 118140960795 + 411491 * 2 ^ 59
def prefixEnd_411491 : Nat := 4983230072969 + 3 ^ 40 * 411491 * 2
def baseEnd_411491 : Nat := 187815704888315354017861

theorem tailTrace_411491 : CollatzResearch.WordTrace tailWord_411491 prefixEnd_411491 187815704888315354017861 := by
  unfold tailWord_411491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15008309752245858912866327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10005539834830572608577551 15008309752245858912866327)
  ·
    refine ⟨22512464628368788369299491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15008309752245858912866327 22512464628368788369299491)
    ·
      refine ⟨33768696942553182553949237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22512464628368788369299491 33768696942553182553949237)
      ·
        refine ⟨3165815338364360864432741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33768696942553182553949237 3165815338364360864432741)
        ·
          refine ⟨593590375943317662081139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3165815338364360864432741 593590375943317662081139)
          ·
            refine ⟨890385563914976493121709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593590375943317662081139 890385563914976493121709)
            ·
              refine ⟨333894586468116184920641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 890385563914976493121709 333894586468116184920641)
              ·
                refine ⟨250420939851087138690481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333894586468116184920641 250420939851087138690481)
                ·
                  refine ⟨187815704888315354017861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250420939851087138690481 187815704888315354017861)
                  ·
                    rfl

theorem cell20_411491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 2].length) (baseStart_411491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411491 prefixEnd_411491 := by exact prefixLift 411491
  have htrace : WordTrace (prefixWord ++ tailWord_411491) baseStart_411491 baseEnd_411491 := by
    simpa [prefixWord, tailWord_411491, baseEnd_411491] using wordTrace_append hprefix tailTrace_411491
  have hstable : (prefixWord ++ tailWord_411491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411491).length < 2 ^ (prefixWord ++ tailWord_411491).sum := by decide
  have hdescent : baseEnd_411491 < baseStart_411491 := by decide
  rcases family_descends (prefixWord ++ tailWord_411491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411502 : List Nat := [4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_411502 : Nat := 118140960795 + 411502 * 2 ^ 59
def prefixEnd_411502 : Nat := 4983230072969 + 3 ^ 40 * 411502 * 2
def baseEnd_411502 : Nat := 62606908529349401550383

theorem tailTrace_411502 : CollatzResearch.WordTrace tailWord_411502 prefixEnd_411502 62606908529349401550383 := by
  unfold tailWord_411502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876088869400750973939595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10005807303470671861011173 1876088869400750973939595)
  ·
    refine ⟨2814133304101126460909393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876088869400750973939595 2814133304101126460909393)
    ·
      refine ⟨2110599978075844845682045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2814133304101126460909393 2110599978075844845682045)
      ·
        refine ⟨791474991778441817130767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2110599978075844845682045 791474991778441817130767)
        ·
          refine ⟨1187212487667662725696151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791474991778441817130767 1187212487667662725696151)
          ·
            refine ⟨1780818731501494088544227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187212487667662725696151 1780818731501494088544227)
            ·
              refine ⟨2671228097252241132816341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780818731501494088544227 2671228097252241132816341)
              ·
                refine ⟨62606908529349401550383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2671228097252241132816341 62606908529349401550383)
                ·
                  rfl

theorem cell20_411502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_411502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411502 prefixEnd_411502 := by exact prefixLift 411502
  have htrace : WordTrace (prefixWord ++ tailWord_411502) baseStart_411502 baseEnd_411502 := by
    simpa [prefixWord, tailWord_411502, baseEnd_411502] using wordTrace_append hprefix tailTrace_411502
  have hstable : (prefixWord ++ tailWord_411502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411502).length < 2 ^ (prefixWord ++ tailWord_411502).sum := by decide
  have hdescent : baseEnd_411502 < baseStart_411502 := by decide
  rcases family_descends (prefixWord ++ tailWord_411502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411523 : List Nat := [1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_411523 : Nat := 118140960795 + 411523 * 2 ^ 59
def prefixEnd_411523 : Nat := 4983230072969 + 3 ^ 40 * 411523 * 2
def baseEnd_411523 : Nat := 62610103520088488317021

theorem tailTrace_411523 : CollatzResearch.WordTrace tailWord_411523 prefixEnd_411523 62610103520088488317021 := by
  unfold tailWord_411523
  simp only [CollatzResearch.WordTrace]
  refine ⟨15009476888129928378031223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10006317925419952252020815 15009476888129928378031223)
  ·
    refine ⟨22514215332194892567046835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15009476888129928378031223 22514215332194892567046835)
    ·
      refine ⟨33771322998292338850570253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22514215332194892567046835 33771322998292338850570253)
      ·
        refine ⟨12664246124359627068963845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33771322998292338850570253 12664246124359627068963845)
        ·
          refine ⟨2374546148317430075430721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12664246124359627068963845 2374546148317430075430721)
          ·
            refine ⟨1780909611238072556573041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374546148317430075430721 1780909611238072556573041)
            ·
              refine ⟨1335682208428554417429781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780909611238072556573041 1335682208428554417429781)
              ·
                refine ⟨62610103520088488317021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1335682208428554417429781 62610103520088488317021)
                ·
                  rfl

theorem cell20_411523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_411523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411523 prefixEnd_411523 := by exact prefixLift 411523
  have htrace : WordTrace (prefixWord ++ tailWord_411523) baseStart_411523 baseEnd_411523 := by
    simpa [prefixWord, tailWord_411523, baseEnd_411523] using wordTrace_append hprefix tailTrace_411523
  have hstable : (prefixWord ++ tailWord_411523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411523).length < 2 ^ (prefixWord ++ tailWord_411523).sum := by decide
  have hdescent : baseEnd_411523 < baseStart_411523 := by decide
  rcases family_descends (prefixWord ++ tailWord_411523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411542 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_411542 : Nat := 118140960795 + 411542 * 2 ^ 59
def prefixEnd_411542 : Nat := 4983230072969 + 3 ^ 40 * 411542 * 2
def baseEnd_411542 : Nat := 187838982677985843317653

theorem tailTrace_411542 : CollatzResearch.WordTrace tailWord_411542 prefixEnd_411542 187838982677985843317653 := by
  unfold tailWord_411542
  simp only [CollatzResearch.WordTrace]
  refine ⟨938135617191318413935805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10006779916707396415315253 938135617191318413935805)
  ·
    refine ⟨351800856446744405225927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 938135617191318413935805 351800856446744405225927)
    ·
      refine ⟨527701284670116607838891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351800856446744405225927 527701284670116607838891)
      ·
        refine ⟨791551927005174911758337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527701284670116607838891 791551927005174911758337)
        ·
          refine ⟨593663945253881183818753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791551927005174911758337 593663945253881183818753)
          ·
            refine ⟨445247958940410887864065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593663945253881183818753 445247958940410887864065)
            ·
              refine ⟨333935969205308165898049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445247958940410887864065 333935969205308165898049)
              ·
                refine ⟨250451976903981124423537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333935969205308165898049 250451976903981124423537)
                ·
                  refine ⟨187838982677985843317653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250451976903981124423537 187838982677985843317653)
                  ·
                    rfl

theorem cell20_411542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_411542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411542 prefixEnd_411542 := by exact prefixLift 411542
  have htrace : WordTrace (prefixWord ++ tailWord_411542) baseStart_411542 baseEnd_411542 := by
    simpa [prefixWord, tailWord_411542, baseEnd_411542] using wordTrace_append hprefix tailTrace_411542
  have hstable : (prefixWord ++ tailWord_411542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411542).length < 2 ^ (prefixWord ++ tailWord_411542).sum := by decide
  have hdescent : baseEnd_411542 < baseStart_411542 := by decide
  rcases family_descends (prefixWord ++ tailWord_411542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411602 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_411602 : Nat := 118140960795 + 411602 * 2 ^ 59
def prefixEnd_411602 : Nat := 4983230072969 + 3 ^ 40 * 411602 * 2
def baseEnd_411602 : Nat := 187866368312892301317407

theorem tailTrace_411602 : CollatzResearch.WordTrace tailWord_411602 prefixEnd_411602 187866368312892301317407 := by
  unfold tailWord_411602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753089563710931217539265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10008238836562483246771373 3753089563710931217539265)
  ·
    refine ⟨2814817172783198413154449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3753089563710931217539265 2814817172783198413154449)
    ·
      refine ⟨2111112879587398809865837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2814817172783198413154449 2111112879587398809865837)
      ·
        refine ⟨791667329845274553699689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2111112879587398809865837 791667329845274553699689)
        ·
          refine ⟨593750497383955915274767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791667329845274553699689 593750497383955915274767)
          ·
            refine ⟨890625746075933872912151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593750497383955915274767 890625746075933872912151)
            ·
              refine ⟨1335938619113900809368227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890625746075933872912151 1335938619113900809368227)
              ·
                refine ⟨2003907928670851214052341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335938619113900809368227 2003907928670851214052341)
                ·
                  refine ⟨187866368312892301317407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2003907928670851214052341 187866368312892301317407)
                  ·
                    rfl

theorem cell20_411602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_411602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411602 prefixEnd_411602 := by exact prefixLift 411602
  have htrace : WordTrace (prefixWord ++ tailWord_411602) baseStart_411602 baseEnd_411602 := by
    simpa [prefixWord, tailWord_411602, baseEnd_411602] using wordTrace_append hprefix tailTrace_411602
  have hstable : (prefixWord ++ tailWord_411602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411602).length < 2 ^ (prefixWord ++ tailWord_411602).sum := by decide
  have hdescent : baseEnd_411602 < baseStart_411602 := by decide
  rcases family_descends (prefixWord ++ tailWord_411602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411609 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_411609 : Nat := 118140960795 + 411609 * 2 ^ 59
def prefixEnd_411609 : Nat := 4983230072969 + 3 ^ 40 * 411609 * 2
def baseEnd_411609 : Nat := 187869563303631388084045

theorem tailTrace_411609 : CollatzResearch.WordTrace tailWord_411609 prefixEnd_411609 187869563303631388084045 := by
  unfold tailWord_411609
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012613565818365065661881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10008409043878910043774587 15012613565818365065661881)
  ·
    refine ⟨11259460174363773799246411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15012613565818365065661881 11259460174363773799246411)
    ·
      refine ⟨16889190261545660698869617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11259460174363773799246411 16889190261545660698869617)
      ·
        refine ⟨12666892696159245524152213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16889190261545660698869617 12666892696159245524152213)
        ·
          refine ⟨593760595132464633944635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12666892696159245524152213 593760595132464633944635)
          ·
            refine ⟨890640892698696950916953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593760595132464633944635 890640892698696950916953)
            ·
              refine ⟨667980669524022713187715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890640892698696950916953 667980669524022713187715)
              ·
                refine ⟨1001971004286034069781573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667980669524022713187715 1001971004286034069781573)
                ·
                  refine ⟨187869563303631388084045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001971004286034069781573 187869563303631388084045)
                  ·
                    rfl

theorem cell20_411609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_411609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411609 prefixEnd_411609 := by exact prefixLift 411609
  have htrace : WordTrace (prefixWord ++ tailWord_411609) baseStart_411609 baseEnd_411609 := by
    simpa [prefixWord, tailWord_411609, baseEnd_411609] using wordTrace_append hprefix tailTrace_411609
  have hstable : (prefixWord ++ tailWord_411609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411609).length < 2 ^ (prefixWord ++ tailWord_411609).sum := by decide
  have hdescent : baseEnd_411609 < baseStart_411609 := by decide
  rcases family_descends (prefixWord ++ tailWord_411609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411629 : List Nat := [1, 5, 1, 4, 2, 1, 2, 4]
def baseStart_411629 : Nat := 118140960795 + 411629 * 2 ^ 59
def prefixEnd_411629 : Nat := 4983230072969 + 3 ^ 40 * 411629 * 2
def baseEnd_411629 : Nat := 62626230616200069139099

theorem tailTrace_411629 : CollatzResearch.WordTrace tailWord_411629 prefixEnd_411629 62626230616200069139099 := by
  unfold tailWord_411629
  simp only [CollatzResearch.WordTrace]
  refine ⟨15013343025745908481389941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10008895350497272320926627 15013343025745908481389941)
  ·
    refine ⟨1407500908663678920130307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15013343025745908481389941 1407500908663678920130307)
    ·
      refine ⟨2111251362995518380195461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407500908663678920130307 2111251362995518380195461)
      ·
        refine ⟨395859630561659696286649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2111251362995518380195461 395859630561659696286649)
        ·
          refine ⟨296894722921244772214987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395859630561659696286649 296894722921244772214987)
          ·
            refine ⟨445342084381867158322481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296894722921244772214987 445342084381867158322481)
            ·
              refine ⟨334006563286400368741861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445342084381867158322481 334006563286400368741861)
              ·
                refine ⟨62626230616200069139099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334006563286400368741861 62626230616200069139099)
                ·
                  rfl

theorem cell20_411629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 4].length) (baseStart_411629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411629 prefixEnd_411629 := by exact prefixLift 411629
  have htrace : WordTrace (prefixWord ++ tailWord_411629) baseStart_411629 baseEnd_411629 := by
    simpa [prefixWord, tailWord_411629, baseEnd_411629] using wordTrace_append hprefix tailTrace_411629
  have hstable : (prefixWord ++ tailWord_411629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411629).length < 2 ^ (prefixWord ++ tailWord_411629).sum := by decide
  have hdescent : baseEnd_411629 < baseStart_411629 := by decide
  rcases family_descends (prefixWord ++ tailWord_411629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411633 : List Nat := [1, 2, 2, 2, 5, 2, 2, 4]
def baseStart_411633 : Nat := 118140960795 + 411633 * 2 ^ 59
def prefixEnd_411633 : Nat := 4983230072969 + 3 ^ 40 * 411633 * 2
def baseEnd_411633 : Nat := 62626839185864657094649

theorem tailTrace_411633 : CollatzResearch.WordTrace tailWord_411633 prefixEnd_411633 62626839185864657094649 := by
  unfold tailWord_411633
  simp only [CollatzResearch.WordTrace]
  refine ⟨15013488917731417164535553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10008992611820944776357035 15013488917731417164535553)
  ·
    refine ⟨11260116688298562873401665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15013488917731417164535553 11260116688298562873401665)
    ·
      refine ⟨8445087516223922155051249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11260116688298562873401665 8445087516223922155051249)
      ·
        refine ⟨6333815637167941616288437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8445087516223922155051249 6333815637167941616288437)
        ·
          refine ⟨593795215984494526527041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6333815637167941616288437 593795215984494526527041)
          ·
            refine ⟨445346411988370894895281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593795215984494526527041 445346411988370894895281)
            ·
              refine ⟨334009808991278171171461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445346411988370894895281 334009808991278171171461)
              ·
                refine ⟨62626839185864657094649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334009808991278171171461 62626839185864657094649)
                ·
                  rfl

theorem cell20_411633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_411633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411633 prefixEnd_411633 := by exact prefixLift 411633
  have htrace : WordTrace (prefixWord ++ tailWord_411633) baseStart_411633 baseEnd_411633 := by
    simpa [prefixWord, tailWord_411633, baseEnd_411633] using wordTrace_append hprefix tailTrace_411633
  have hstable : (prefixWord ++ tailWord_411633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411633).length < 2 ^ (prefixWord ++ tailWord_411633).sum := by decide
  have hdescent : baseEnd_411633 < baseStart_411633 := by decide
  rcases family_descends (prefixWord ++ tailWord_411633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411644 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_411644 : Nat := 118140960795 + 411644 * 2 ^ 59
def prefixEnd_411644 : Nat := 4983230072969 + 3 ^ 40 * 411644 * 2
def baseEnd_411644 : Nat := 187885538257326821917235

theorem tailTrace_411644 : CollatzResearch.WordTrace tailWord_411644 prefixEnd_411644 187885538257326821917235 := by
  unfold tailWord_411644
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506945060345783021592993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10009260080461044028790657 7506945060345783021592993)
  ·
    refine ⟨5630208795259337266194745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7506945060345783021592993 5630208795259337266194745)
    ·
      refine ⟨4222656596444502949646059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5630208795259337266194745 4222656596444502949646059)
      ·
        refine ⟨6333984894666754424469089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222656596444502949646059 6333984894666754424469089)
        ·
          refine ⟨4750488671000065818351817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6333984894666754424469089 4750488671000065818351817)
          ·
            refine ⟨3562866503250049363763863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4750488671000065818351817 3562866503250049363763863)
            ·
              refine ⟨5344299754875074045645795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3562866503250049363763863 5344299754875074045645795)
              ·
                refine ⟨8016449632312611068468693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344299754875074045645795 8016449632312611068468693)
                ·
                  refine ⟨187885538257326821917235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8016449632312611068468693 187885538257326821917235)
                  ·
                    rfl

theorem cell20_411644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_411644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411644 prefixEnd_411644 := by exact prefixLift 411644
  have htrace : WordTrace (prefixWord ++ tailWord_411644) baseStart_411644 baseEnd_411644 := by
    simpa [prefixWord, tailWord_411644, baseEnd_411644] using wordTrace_append hprefix tailTrace_411644
  have hstable : (prefixWord ++ tailWord_411644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411644).length < 2 ^ (prefixWord ++ tailWord_411644).sum := by decide
  have hdescent : baseEnd_411644 < baseStart_411644 := by decide
  rcases family_descends (prefixWord ++ tailWord_411644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411651 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_411651 : Nat := 118140960795 + 411651 * 2 ^ 59
def prefixEnd_411651 : Nat := 4983230072969 + 3 ^ 40 * 411651 * 2
def baseEnd_411651 : Nat := 187888733248065908683873

theorem tailTrace_411651 : CollatzResearch.WordTrace tailWord_411651 prefixEnd_411651 187888733248065908683873 := by
  unfold tailWord_411651
  simp only [CollatzResearch.WordTrace]
  refine ⟨15014145431666206238690807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10009430287777470825793871 15014145431666206238690807)
  ·
    refine ⟨22521218147499309358036211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15014145431666206238690807 22521218147499309358036211)
    ·
      refine ⟨33781827221248964037054317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22521218147499309358036211 33781827221248964037054317)
      ·
        refine ⟨12668185207968361513895369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33781827221248964037054317 12668185207968361513895369)
        ·
          refine ⟨9501138905976271135421527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12668185207968361513895369 9501138905976271135421527)
          ·
            refine ⟨14251708358964406703132291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9501138905976271135421527 14251708358964406703132291)
            ·
              refine ⟨21377562538446610054698437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14251708358964406703132291 21377562538446610054698437)
              ·
                refine ⟨4008292975958739385255957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21377562538446610054698437 4008292975958739385255957)
                ·
                  refine ⟨187888733248065908683873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4008292975958739385255957 187888733248065908683873)
                  ·
                    rfl

theorem cell20_411651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_411651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411651 prefixEnd_411651 := by exact prefixLift 411651
  have htrace : WordTrace (prefixWord ++ tailWord_411651) baseStart_411651 baseEnd_411651 := by
    simpa [prefixWord, tailWord_411651, baseEnd_411651] using wordTrace_append hprefix tailTrace_411651
  have hstable : (prefixWord ++ tailWord_411651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411651).length < 2 ^ (prefixWord ++ tailWord_411651).sum := by decide
  have hdescent : baseEnd_411651 < baseStart_411651 := by decide
  rcases family_descends (prefixWord ++ tailWord_411651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411702 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_411702 : Nat := 118140960795 + 411702 * 2 ^ 59
def prefixEnd_411702 : Nat := 4983230072969 + 3 ^ 40 * 411702 * 2
def baseEnd_411702 : Nat := 187912011037736397983665

theorem tailTrace_411702 : CollatzResearch.WordTrace tailWord_411702 prefixEnd_411702 187912011037736397983665 := by
  unfold tailWord_411702
  simp only [CollatzResearch.WordTrace]
  refine ⟨938500347155090121799835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10010670369654294632531573 938500347155090121799835)
  ·
    refine ⟨1407750520732635182699753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 938500347155090121799835 1407750520732635182699753)
    ·
      refine ⟨1055812890549476387024815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1407750520732635182699753 1055812890549476387024815)
      ·
        refine ⟨1583719335824214580537223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055812890549476387024815 1583719335824214580537223)
        ·
          refine ⟨2375579003736321870805835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583719335824214580537223 2375579003736321870805835)
          ·
            refine ⟨3563368505604482806208753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375579003736321870805835 3563368505604482806208753)
            ·
              refine ⟨2672526379203362104656565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563368505604482806208753 2672526379203362104656565)
              ·
                refine ⟨250549348050315197311553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2672526379203362104656565 250549348050315197311553)
                ·
                  refine ⟨187912011037736397983665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250549348050315197311553 187912011037736397983665)
                  ·
                    rfl

theorem cell20_411702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_411702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411702 prefixEnd_411702 := by exact prefixLift 411702
  have htrace : WordTrace (prefixWord ++ tailWord_411702) baseStart_411702 baseEnd_411702 := by
    simpa [prefixWord, tailWord_411702, baseEnd_411702] using wordTrace_append hprefix tailTrace_411702
  have hstable : (prefixWord ++ tailWord_411702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411702).length < 2 ^ (prefixWord ++ tailWord_411702).sum := by decide
  have hdescent : baseEnd_411702 < baseStart_411702 := by decide
  rcases family_descends (prefixWord ++ tailWord_411702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411713 : List Nat := [1, 2, 5, 1, 2, 9]
def baseStart_411713 : Nat := 118140960795 + 411713 * 2 ^ 59
def prefixEnd_411713 : Nat := 4983230072969 + 3 ^ 40 * 411713 * 2
def baseEnd_411713 : Nat := 6959890064350712911739

theorem tailTrace_411713 : CollatzResearch.WordTrace tailWord_411713 prefixEnd_411713 6959890064350712911739 := by
  unfold tailWord_411713
  simp only [CollatzResearch.WordTrace]
  refine ⟨15016406757441590827447793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10010937838294393884965195 15016406757441590827447793)
  ·
    refine ⟨11262305068081193120585845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15016406757441590827447793 11262305068081193120585845)
    ·
      refine ⟨1055841100132611855054923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11262305068081193120585845 1055841100132611855054923)
      ·
        refine ⟨1583761650198917782582385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055841100132611855054923 1583761650198917782582385)
        ·
          refine ⟨1187821237649188336936789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583761650198917782582385 1187821237649188336936789)
          ·
            refine ⟨6959890064350712911739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1187821237649188336936789 6959890064350712911739)
            ·
              rfl

theorem cell20_411713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 9].length) (baseStart_411713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411713 prefixEnd_411713 := by exact prefixLift 411713
  have htrace : WordTrace (prefixWord ++ tailWord_411713) baseStart_411713 baseEnd_411713 := by
    simpa [prefixWord, tailWord_411713, baseEnd_411713] using wordTrace_append hprefix tailTrace_411713
  have hstable : (prefixWord ++ tailWord_411713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411713).length < 2 ^ (prefixWord ++ tailWord_411713).sum := by decide
  have hdescent : baseEnd_411713 < baseStart_411713 := by decide
  rcases family_descends (prefixWord ++ tailWord_411713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411744 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_411744 : Nat := 118140960795 + 411744 * 2 ^ 59
def prefixEnd_411744 : Nat := 4983230072969 + 3 ^ 40 * 411744 * 2
def baseEnd_411744 : Nat := 187931180982170918583493

theorem tailTrace_411744 : CollatzResearch.WordTrace tailWord_411744 prefixEnd_411744 187931180982170918583493 := by
  unfold tailWord_411744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508768710164641560913143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10011691613552855414550857 7508768710164641560913143)
  ·
    refine ⟨11263153065246962341369715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7508768710164641560913143 11263153065246962341369715)
    ·
      refine ⟨16894729597870443512054573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11263153065246962341369715 16894729597870443512054573)
      ·
        refine ⟨6335523599201416317020465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16894729597870443512054573 6335523599201416317020465)
        ·
          refine ⟨4751642699401062237765349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6335523599201416317020465 4751642699401062237765349)
          ·
            refine ⟨890933006137699169581003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4751642699401062237765349 890933006137699169581003)
            ·
              refine ⟨1336399509206548754371505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890933006137699169581003 1336399509206548754371505)
              ·
                refine ⟨1002299631904911565778629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336399509206548754371505 1002299631904911565778629)
                ·
                  refine ⟨187931180982170918583493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002299631904911565778629 187931180982170918583493)
                  ·
                    rfl

theorem cell20_411744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_411744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411744 prefixEnd_411744 := by exact prefixLift 411744
  have htrace : WordTrace (prefixWord ++ tailWord_411744) baseStart_411744 baseEnd_411744 := by
    simpa [prefixWord, tailWord_411744, baseEnd_411744] using wordTrace_append hprefix tailTrace_411744
  have hstable : (prefixWord ++ tailWord_411744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411744).length < 2 ^ (prefixWord ++ tailWord_411744).sum := by decide
  have hdescent : baseEnd_411744 < baseStart_411744 := by decide
  rcases family_descends (prefixWord ++ tailWord_411744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411761 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 2]
def baseStart_411761 : Nat := 118140960795 + 411761 * 2 ^ 59
def prefixEnd_411761 : Nat := 4983230072969 + 3 ^ 40 * 411761 * 2
def baseEnd_411761 : Nat := 187938940245394415016757

theorem tailTrace_411761 : CollatzResearch.WordTrace tailWord_411761 prefixEnd_411761 187938940245394415016757 := by
  unfold tailWord_411761
  simp only [CollatzResearch.WordTrace]
  refine ⟨15018157461267695025195137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10012104974178463350130091 15018157461267695025195137)
  ·
    refine ⟨11263618095950771268896353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15018157461267695025195137 11263618095950771268896353)
    ·
      refine ⟨8447713571963078451672265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11263618095950771268896353 8447713571963078451672265)
      ·
        refine ⟨6335785178972308838754199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8447713571963078451672265 6335785178972308838754199)
        ·
          refine ⟨9503677768458463258131299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6335785178972308838754199 9503677768458463258131299)
          ·
            refine ⟨14255516652687694887196949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9503677768458463258131299 14255516652687694887196949)
            ·
              refine ⟨668227343094735697837357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14255516652687694887196949 668227343094735697837357)
              ·
                refine ⟨250585253660525886689009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 668227343094735697837357 250585253660525886689009)
                ·
                  refine ⟨187938940245394415016757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250585253660525886689009 187938940245394415016757)
                  ·
                    rfl

theorem cell20_411761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_411761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411761 prefixEnd_411761 := by exact prefixLift 411761
  have htrace : WordTrace (prefixWord ++ tailWord_411761) baseStart_411761 baseEnd_411761 := by
    simpa [prefixWord, tailWord_411761, baseEnd_411761] using wordTrace_append hprefix tailTrace_411761
  have hstable : (prefixWord ++ tailWord_411761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411761).length < 2 ^ (prefixWord ++ tailWord_411761).sum := by decide
  have hdescent : baseEnd_411761 < baseStart_411761 := by decide
  rcases family_descends (prefixWord ++ tailWord_411761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411802 : List Nat := [3, 1, 1, 5, 3, 1, 2, 4]
def baseStart_411802 : Nat := 118140960795 + 411802 * 2 ^ 59
def prefixEnd_411802 : Nat := 4983230072969 + 3 ^ 40 * 411802 * 2
def baseEnd_411802 : Nat := 62652551254193498216641

theorem tailTrace_411802 : CollatzResearch.WordTrace tailWord_411802 prefixEnd_411802 62652551254193498216641 := by
  unfold tailWord_411802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754913213529789756859415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10013101902746106018291773 3754913213529789756859415)
  ·
    refine ⟨5632369820294684635289123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3754913213529789756859415 5632369820294684635289123)
    ·
      refine ⟨8448554730442026952933685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5632369820294684635289123 8448554730442026952933685)
      ·
        refine ⟨792052005978940026837533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8448554730442026952933685 792052005978940026837533)
        ·
          refine ⟨297019502242102510064075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 792052005978940026837533 297019502242102510064075)
          ·
            refine ⟨445529253363153765096113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297019502242102510064075 445529253363153765096113)
            ·
              refine ⟨334146940022365323822085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445529253363153765096113 334146940022365323822085)
              ·
                refine ⟨62652551254193498216641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334146940022365323822085 62652551254193498216641)
                ·
                  rfl

theorem cell20_411802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_411802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411802 prefixEnd_411802 := by exact prefixLift 411802
  have htrace : WordTrace (prefixWord ++ tailWord_411802) baseStart_411802 baseEnd_411802 := by
    simpa [prefixWord, tailWord_411802, baseEnd_411802] using wordTrace_append hprefix tailTrace_411802
  have hstable : (prefixWord ++ tailWord_411802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411802).length < 2 ^ (prefixWord ++ tailWord_411802).sum := by decide
  have hdescent : baseEnd_411802 < baseStart_411802 := by decide
  rcases family_descends (prefixWord ++ tailWord_411802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_411803 : Nat := 118140960795 + 411803 * 2 ^ 59
def prefixEnd_411803 : Nat := 4983230072969 + 3 ^ 40 * 411803 * 2
def baseEnd_411803 : Nat := 187958110189828935616585

theorem tailTrace_411803 : CollatzResearch.WordTrace tailWord_411803 prefixEnd_411803 187958110189828935616585 := by
  unfold tailWord_411803
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019689327115536198224063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10013126218077024132149375 15019689327115536198224063)
  ·
    refine ⟨22529533990673304297336095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15019689327115536198224063 22529533990673304297336095)
    ·
      refine ⟨33794300986009956446004143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22529533990673304297336095 33794300986009956446004143)
      ·
        refine ⟨50691451479014934669006215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33794300986009956446004143 50691451479014934669006215)
        ·
          refine ⟨76037177218522402003509323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50691451479014934669006215 76037177218522402003509323)
          ·
            refine ⟨114055765827783603005263985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76037177218522402003509323 114055765827783603005263985)
            ·
              refine ⟨85541824370837702253947989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114055765827783603005263985 85541824370837702253947989)
              ·
                refine ⟨1002443254345754323288453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 85541824370837702253947989 1002443254345754323288453)
                ·
                  refine ⟨187958110189828935616585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002443254345754323288453 187958110189828935616585)
                  ·
                    rfl

theorem cell20_411803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_411803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411803 prefixEnd_411803 := by exact prefixLift 411803
  have htrace : WordTrace (prefixWord ++ tailWord_411803) baseStart_411803 baseEnd_411803 := by
    simpa [prefixWord, tailWord_411803, baseEnd_411803] using wordTrace_append hprefix tailTrace_411803
  have hstable : (prefixWord ++ tailWord_411803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411803).length < 2 ^ (prefixWord ++ tailWord_411803).sum := by decide
  have hdescent : baseEnd_411803 < baseStart_411803 := by decide
  rcases family_descends (prefixWord ++ tailWord_411803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411834 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_411834 : Nat := 118140960795 + 411834 * 2 ^ 59
def prefixEnd_411834 : Nat := 4983230072969 + 3 ^ 40 * 411834 * 2
def baseEnd_411834 : Nat := 187972259434530605583125

theorem tailTrace_411834 : CollatzResearch.WordTrace tailWord_411834 prefixEnd_411834 187972259434530605583125 := by
  unfold tailWord_411834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755204997500807123150639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10013879993335485661735037 3755204997500807123150639)
  ·
    refine ⟨5632807496251210684725959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3755204997500807123150639 5632807496251210684725959)
    ·
      refine ⟨8449211244376816027088939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5632807496251210684725959 8449211244376816027088939)
      ·
        refine ⟨12673816866565224040633409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8449211244376816027088939 12673816866565224040633409)
        ·
          refine ⟨9505362649923918030475057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12673816866565224040633409 9505362649923918030475057)
          ·
            refine ⟨7129021987442938522856293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9505362649923918030475057 7129021987442938522856293)
            ·
              refine ⟨1336691622645550973035555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7129021987442938522856293 1336691622645550973035555)
              ·
                refine ⟨2005037433968326459553333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336691622645550973035555 2005037433968326459553333)
                ·
                  refine ⟨187972259434530605583125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2005037433968326459553333 187972259434530605583125)
                  ·
                    rfl

theorem cell20_411834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_411834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411834 prefixEnd_411834 := by exact prefixLift 411834
  have htrace : WordTrace (prefixWord ++ tailWord_411834) baseStart_411834 baseEnd_411834 := by
    simpa [prefixWord, tailWord_411834, baseEnd_411834] using wordTrace_append hprefix tailTrace_411834
  have hstable : (prefixWord ++ tailWord_411834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411834).length < 2 ^ (prefixWord ++ tailWord_411834).sum := by decide
  have hdescent : baseEnd_411834 < baseStart_411834 := by decide
  rcases family_descends (prefixWord ++ tailWord_411834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411844 : List Nat := [2, 3, 3, 1, 2, 2, 2, 5]
def baseStart_411844 : Nat := 118140960795 + 411844 * 2 ^ 59
def prefixEnd_411844 : Nat := 4983230072969 + 3 ^ 40 * 411844 * 2
def baseEnd_411844 : Nat := 62658941235671671749917

theorem tailTrace_411844 : CollatzResearch.WordTrace tailWord_411844 prefixEnd_411844 62658941235671671749917 := by
  unfold tailWord_411844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510592359983500100233293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10014123146644666800311057 7510592359983500100233293)
  ·
    refine ⟨2816472134993812537587485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7510592359983500100233293 2816472134993812537587485)
    ·
      refine ⟨1056177050622679701595307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2816472134993812537587485 1056177050622679701595307)
      ·
        refine ⟨1584265575934019552392961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056177050622679701595307 1584265575934019552392961)
        ·
          refine ⟨1188199181950514664294721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584265575934019552392961 1188199181950514664294721)
          ·
            refine ⟨891149386462885998221041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188199181950514664294721 891149386462885998221041)
            ·
              refine ⟨668362039847164498665781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891149386462885998221041 668362039847164498665781)
              ·
                refine ⟨62658941235671671749917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 668362039847164498665781 62658941235671671749917)
                ·
                  rfl

theorem cell20_411844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_411844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411844 prefixEnd_411844 := by exact prefixLift 411844
  have htrace : WordTrace (prefixWord ++ tailWord_411844) baseStart_411844 baseEnd_411844 := by
    simpa [prefixWord, tailWord_411844, baseEnd_411844] using wordTrace_append hprefix tailTrace_411844
  have hstable : (prefixWord ++ tailWord_411844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411844).length < 2 ^ (prefixWord ++ tailWord_411844).sum := by decide
  have hdescent : baseEnd_411844 < baseStart_411844 := by decide
  rcases family_descends (prefixWord ++ tailWord_411844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411906 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_411906 : Nat := 118140960795 + 411906 * 2 ^ 59
def prefixEnd_411906 : Nat := 4983230072969 + 3 ^ 40 * 411906 * 2
def baseEnd_411906 : Nat := 188005122196418355182831

theorem tailTrace_411906 : CollatzResearch.WordTrace tailWord_411906 prefixEnd_411906 188005122196418355182831 := by
  unfold tailWord_411906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755861511435596197305893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10015630697161589859482381 3755861511435596197305893)
  ·
    refine ⟨704224033394174286994855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3755861511435596197305893 704224033394174286994855)
    ·
      refine ⟨1056336050091261430492283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704224033394174286994855 1056336050091261430492283)
      ·
        refine ⟨1584504075136892145738425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056336050091261430492283 1584504075136892145738425)
        ·
          refine ⟨1188378056352669109303819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584504075136892145738425 1188378056352669109303819)
          ·
            refine ⟨1782567084529003663955729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188378056352669109303819 1782567084529003663955729)
            ·
              refine ⟨1336925313396752747966797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1782567084529003663955729 1336925313396752747966797)
              ·
                refine ⟨501346992523782280487549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1336925313396752747966797 501346992523782280487549)
                ·
                  refine ⟨188005122196418355182831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501346992523782280487549 188005122196418355182831)
                  ·
                    rfl

theorem cell20_411906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_411906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411906 prefixEnd_411906 := by exact prefixLift 411906
  have htrace : WordTrace (prefixWord ++ tailWord_411906) baseStart_411906 baseEnd_411906 := by
    simpa [prefixWord, tailWord_411906, baseEnd_411906] using wordTrace_append hprefix tailTrace_411906
  have hstable : (prefixWord ++ tailWord_411906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411906).length < 2 ^ (prefixWord ++ tailWord_411906).sum := by decide
  have hdescent : baseEnd_411906 < baseStart_411906 := by decide
  rcases family_descends (prefixWord ++ tailWord_411906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411930 : List Nat := [3, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_411930 : Nat := 118140960795 + 411930 * 2 ^ 59
def prefixEnd_411930 : Nat := 4983230072969 + 3 ^ 40 * 411930 * 2
def baseEnd_411930 : Nat := 188016076450380938382733

theorem tailTrace_411930 : CollatzResearch.WordTrace tailWord_411930 prefixEnd_411930 188016076450380938382733 := by
  unfold tailWord_411930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756080349413859222024311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10016214265103624592064829 3756080349413859222024311)
  ·
    refine ⟨5634120524120788833036467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3756080349413859222024311 5634120524120788833036467)
    ·
      refine ⟨8451180786181183249554701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5634120524120788833036467 8451180786181183249554701)
      ·
        refine ⟨3169192794817943718583013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8451180786181183249554701 3169192794817943718583013)
        ·
          refine ⟨594223649028364447234315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3169192794817943718583013 594223649028364447234315)
          ·
            refine ⟨891335473542546670851473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594223649028364447234315 891335473542546670851473)
            ·
              refine ⟨668501605156910003138605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891335473542546670851473 668501605156910003138605)
              ·
                refine ⟨250688101933841251176977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 668501605156910003138605 250688101933841251176977)
                ·
                  refine ⟨188016076450380938382733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250688101933841251176977 188016076450380938382733)
                  ·
                    rfl

theorem cell20_411930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_411930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411930 prefixEnd_411930 := by exact prefixLift 411930
  have htrace : WordTrace (prefixWord ++ tailWord_411930) baseStart_411930 baseEnd_411930 := by
    simpa [prefixWord, tailWord_411930, baseEnd_411930] using wordTrace_append hprefix tailTrace_411930
  have hstable : (prefixWord ++ tailWord_411930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411930).length < 2 ^ (prefixWord ++ tailWord_411930).sum := by decide
  have hdescent : baseEnd_411930 < baseStart_411930 := by decide
  rcases family_descends (prefixWord ++ tailWord_411930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411941 : List Nat := [1, 3, 1, 2, 5, 1, 7]
def baseStart_411941 : Nat := 118140960795 + 411941 * 2 ^ 59
def prefixEnd_411941 : Nat := 4983230072969 + 3 ^ 40 * 411941 * 2
def baseEnd_411941 : Nat := 20891233016679309890669

theorem tailTrace_411941 : CollatzResearch.WordTrace tailWord_411941 prefixEnd_411941 20891233016679309890669 := by
  unfold tailWord_411941
  simp only [CollatzResearch.WordTrace]
  refine ⟨15024722600615585766747677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10016481733743723844498451 15024722600615585766747677)
  ·
    refine ⟨5634270975230844662530379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15024722600615585766747677 5634270975230844662530379)
    ·
      refine ⟨8451406462846266993795569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5634270975230844662530379 8451406462846266993795569)
      ·
        refine ⟨6338554847134700245346677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8451406462846266993795569 6338554847134700245346677)
        ·
          refine ⟨594239516918878148001251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6338554847134700245346677 594239516918878148001251)
          ·
            refine ⟨891359275378317222001877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594239516918878148001251 891359275378317222001877)
            ·
              refine ⟨20891233016679309890669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 891359275378317222001877 20891233016679309890669)
              ·
                rfl

theorem cell20_411941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_411941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411941 prefixEnd_411941 := by exact prefixLift 411941
  have htrace : WordTrace (prefixWord ++ tailWord_411941) baseStart_411941 baseEnd_411941 := by
    simpa [prefixWord, tailWord_411941, baseEnd_411941] using wordTrace_append hprefix tailTrace_411941
  have hstable : (prefixWord ++ tailWord_411941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411941).length < 2 ^ (prefixWord ++ tailWord_411941).sum := by decide
  have hdescent : baseEnd_411941 < baseStart_411941 := by decide
  rcases family_descends (prefixWord ++ tailWord_411941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411986 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_411986 : Nat := 118140960795 + 411986 * 2 ^ 59
def prefixEnd_411986 : Nat := 4983230072969 + 3 ^ 40 * 411986 * 2
def baseEnd_411986 : Nat := 188041636376293632515837

theorem tailTrace_411986 : CollatzResearch.WordTrace tailWord_411986 prefixEnd_411986 188041636376293632515837 := by
  unfold tailWord_411986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756590971363139613033953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10017575923635038968090541 3756590971363139613033953)
  ·
    refine ⟨2817443228522354709775465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3756590971363139613033953 2817443228522354709775465)
    ·
      refine ⟨2113082421391766032331599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2817443228522354709775465 2113082421391766032331599)
      ·
        refine ⟨3169623632087649048497399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113082421391766032331599 3169623632087649048497399)
        ·
          refine ⟨4754435448131473572746099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3169623632087649048497399 4754435448131473572746099)
          ·
            refine ⟨7131653172197210359119149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754435448131473572746099 7131653172197210359119149)
            ·
              refine ⟨2674369939573953884669681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7131653172197210359119149 2674369939573953884669681)
              ·
                refine ⟨2005777454680465413502261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2674369939573953884669681 2005777454680465413502261)
                ·
                  refine ⟨188041636376293632515837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2005777454680465413502261 188041636376293632515837)
                  ·
                    rfl

theorem cell20_411986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_411986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411986 prefixEnd_411986 := by exact prefixLift 411986
  have htrace : WordTrace (prefixWord ++ tailWord_411986) baseStart_411986 baseEnd_411986 := by
    simpa [prefixWord, tailWord_411986, baseEnd_411986] using wordTrace_append hprefix tailTrace_411986
  have hstable : (prefixWord ++ tailWord_411986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411986).length < 2 ^ (prefixWord ++ tailWord_411986).sum := by decide
  have hdescent : baseEnd_411986 < baseStart_411986 := by decide
  rcases family_descends (prefixWord ++ tailWord_411986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411998 : List Nat := [4, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_411998 : Nat := 118140960795 + 411998 * 2 ^ 59
def prefixEnd_411998 : Nat := 4983230072969 + 3 ^ 40 * 411998 * 2
def baseEnd_411998 : Nat := 188047113503274924115789

theorem tailTrace_411998 : CollatzResearch.WordTrace tailWord_411998 prefixEnd_411998 188047113503274924115789 := by
  unfold tailWord_411998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878350195176135562696581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10017867707606056334381765 1878350195176135562696581)
  ·
    refine ⟨352190661595525418005609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1878350195176135562696581 352190661595525418005609)
    ·
      refine ⟨264142996196644063504207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352190661595525418005609 264142996196644063504207)
      ·
        refine ⟨396214494294966095256311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264142996196644063504207 396214494294966095256311)
        ·
          refine ⟨594321741442449142884467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396214494294966095256311 594321741442449142884467)
          ·
            refine ⟨891482612163673714326701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594321741442449142884467 891482612163673714326701)
            ·
              refine ⟨334305979561377642872513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891482612163673714326701 334305979561377642872513)
              ·
                refine ⟨250729484671033232154385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334305979561377642872513 250729484671033232154385)
                ·
                  refine ⟨188047113503274924115789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250729484671033232154385 188047113503274924115789)
                  ·
                    rfl

theorem cell20_411998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_411998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_411998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_411998 prefixEnd_411998 := by exact prefixLift 411998
  have htrace : WordTrace (prefixWord ++ tailWord_411998) baseStart_411998 baseEnd_411998 := by
    simpa [prefixWord, tailWord_411998, baseEnd_411998] using wordTrace_append hprefix tailTrace_411998
  have hstable : (prefixWord ++ tailWord_411998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411998).length < 2 ^ (prefixWord ++ tailWord_411998).sum := by decide
  have hdescent : baseEnd_411998 < baseStart_411998 := by decide
  rcases family_descends (prefixWord ++ tailWord_411998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412061 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 2]
def baseStart_412061 : Nat := 118140960795 + 412061 * 2 ^ 59
def prefixEnd_412061 : Nat := 4983230072969 + 3 ^ 40 * 412061 * 2
def baseEnd_412061 : Nat := 188075868419926705015531

theorem tailTrace_412061 : CollatzResearch.WordTrace tailWord_412061 prefixEnd_412061 188075868419926705015531 := by
  unfold tailWord_412061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15029099360180846261116037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10019399573453897507410691 15029099360180846261116037)
  ·
    refine ⟨2817956130033908673959257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15029099360180846261116037 2817956130033908673959257)
    ·
      refine ⟨2113467097525431505469443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2817956130033908673959257 2113467097525431505469443)
      ·
        refine ⟨3170200646288147258204165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113467097525431505469443 3170200646288147258204165)
        ·
          refine ⟨594412621179027610913281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3170200646288147258204165 594412621179027610913281)
          ·
            refine ⟨445809465884270708184961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594412621179027610913281 445809465884270708184961)
            ·
              refine ⟨334357099413203031138721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445809465884270708184961 334357099413203031138721)
              ·
                refine ⟨250767824559902273354041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334357099413203031138721 250767824559902273354041)
                ·
                  refine ⟨188075868419926705015531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250767824559902273354041 188075868419926705015531)
                  ·
                    rfl

theorem cell20_412061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_412061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412061 prefixEnd_412061 := by exact prefixLift 412061
  have htrace : WordTrace (prefixWord ++ tailWord_412061) baseStart_412061 baseEnd_412061 := by
    simpa [prefixWord, tailWord_412061, baseEnd_412061] using wordTrace_append hprefix tailTrace_412061
  have hstable : (prefixWord ++ tailWord_412061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412061).length < 2 ^ (prefixWord ++ tailWord_412061).sum := by decide
  have hdescent : baseEnd_412061 < baseStart_412061 := by decide
  rcases family_descends (prefixWord ++ tailWord_412061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412069 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 4]
def baseStart_412069 : Nat := 118140960795 + 412069 * 2 ^ 59
def prefixEnd_412069 : Nat := 4983230072969 + 3 ^ 40 * 412069 * 2
def baseEnd_412069 : Nat := 188079519837914232748831

theorem tailTrace_412069 : CollatzResearch.WordTrace tailWord_412069 prefixEnd_412069 188079519837914232748831 := by
  unfold tailWord_412069
  simp only [CollatzResearch.WordTrace]
  refine ⟨15029391144151863627407261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10019594096101242418271507 15029391144151863627407261)
  ·
    refine ⟨5636021679056948860277723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15029391144151863627407261 5636021679056948860277723)
    ·
      refine ⟨8454032518585423290416585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636021679056948860277723 8454032518585423290416585)
      ·
        refine ⟨6340524388939067467812439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8454032518585423290416585 6340524388939067467812439)
        ·
          refine ⟨9510786583408601201718659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340524388939067467812439 9510786583408601201718659)
          ·
            refine ⟨14266179875112901802577989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510786583408601201718659 14266179875112901802577989)
            ·
              refine ⟨2674908726583669087983373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14266179875112901802577989 2674908726583669087983373)
              ·
                refine ⟨1003090772468875907993765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2674908726583669087983373 1003090772468875907993765)
                ·
                  refine ⟨188079519837914232748831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003090772468875907993765 188079519837914232748831)
                  ·
                    rfl

theorem cell20_412069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_412069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412069 prefixEnd_412069 := by exact prefixLift 412069
  have htrace : WordTrace (prefixWord ++ tailWord_412069) baseStart_412069 baseEnd_412069 := by
    simpa [prefixWord, tailWord_412069, baseEnd_412069] using wordTrace_append hprefix tailTrace_412069
  have hstable : (prefixWord ++ tailWord_412069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412069).length < 2 ^ (prefixWord ++ tailWord_412069).sum := by decide
  have hdescent : baseEnd_412069 < baseStart_412069 := by decide
  rcases family_descends (prefixWord ++ tailWord_412069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412072 : List Nat := [2, 1, 6, 1, 1, 1, 3, 5]
def baseStart_412072 : Nat := 118140960795 + 412072 * 2 ^ 59
def prefixEnd_412072 : Nat := 4983230072969 + 3 ^ 40 * 412072 * 2
def baseEnd_412072 : Nat := 62693629706553185216273

theorem tailTrace_412072 : CollatzResearch.WordTrace tailWord_412072 prefixEnd_412072 62693629706553185216273 := by
  unfold tailWord_412072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514750281570497569883235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10019667042093996759844313 7514750281570497569883235)
  ·
    refine ⟨11272125422355746354824853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7514750281570497569883235 11272125422355746354824853)
    ·
      refine ⟨528380879172925610382415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11272125422355746354824853 528380879172925610382415)
      ·
        refine ⟨792571318759388415573623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528380879172925610382415 792571318759388415573623)
        ·
          refine ⟨1188856978139082623360435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792571318759388415573623 1188856978139082623360435)
          ·
            refine ⟨1783285467208623935040653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188856978139082623360435 1783285467208623935040653)
            ·
              refine ⟨668732050203233975640245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1783285467208623935040653 668732050203233975640245)
              ·
                refine ⟨62693629706553185216273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 668732050203233975640245 62693629706553185216273)
                ·
                  rfl

theorem cell20_412072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_412072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412072 prefixEnd_412072 := by exact prefixLift 412072
  have htrace : WordTrace (prefixWord ++ tailWord_412072) baseStart_412072 baseEnd_412072 := by
    simpa [prefixWord, tailWord_412072, baseEnd_412072] using wordTrace_append hprefix tailTrace_412072
  have hstable : (prefixWord ++ tailWord_412072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412072).length < 2 ^ (prefixWord ++ tailWord_412072).sum := by decide
  have hdescent : baseEnd_412072 < baseStart_412072 := by decide
  rcases family_descends (prefixWord ++ tailWord_412072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412083 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_412083 : Nat := 118140960795 + 412083 * 2 ^ 59
def prefixEnd_412083 : Nat := 4983230072969 + 3 ^ 40 * 412083 * 2
def baseEnd_412083 : Nat := 188085909819392406282107

theorem tailTrace_412083 : CollatzResearch.WordTrace tailWord_412083 prefixEnd_412083 188085909819392406282107 := by
  unfold tailWord_412083
  simp only [CollatzResearch.WordTrace]
  refine ⟨15029901766101144018416903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10019934510734096012277935 15029901766101144018416903)
  ·
    refine ⟨22544852649151716027625355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15029901766101144018416903 22544852649151716027625355)
    ·
      refine ⟨33817278973727574041438033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22544852649151716027625355 33817278973727574041438033)
      ·
        refine ⟨25362959230295680531078525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33817278973727574041438033 25362959230295680531078525)
        ·
          refine ⟨9511109711360880199154447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25362959230295680531078525 9511109711360880199154447)
          ·
            refine ⟨14266664567041320298731671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9511109711360880199154447 14266664567041320298731671)
            ·
              refine ⟨21399996850561980448097507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14266664567041320298731671 21399996850561980448097507)
              ·
                refine ⟨32099995275842970672146261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21399996850561980448097507 32099995275842970672146261)
                ·
                  refine ⟨188085909819392406282107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32099995275842970672146261 188085909819392406282107)
                  ·
                    rfl

theorem cell20_412083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_412083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412083 prefixEnd_412083 := by exact prefixLift 412083
  have htrace : WordTrace (prefixWord ++ tailWord_412083) baseStart_412083 baseEnd_412083 := by
    simpa [prefixWord, tailWord_412083, baseEnd_412083] using wordTrace_append hprefix tailTrace_412083
  have hstable : (prefixWord ++ tailWord_412083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412083).length < 2 ^ (prefixWord ++ tailWord_412083).sum := by decide
  have hdescent : baseEnd_412083 < baseStart_412083 := by decide
  rcases family_descends (prefixWord ++ tailWord_412083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412103 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 2]
def baseStart_412103 : Nat := 118140960795 + 412103 * 2 ^ 59
def prefixEnd_412103 : Nat := 4983230072969 + 3 ^ 40 * 412103 * 2
def baseEnd_412103 : Nat := 188095038364361225615359

theorem tailTrace_412103 : CollatzResearch.WordTrace tailWord_412103 prefixEnd_412103 188095038364361225615359 := by
  unfold tailWord_412103
  simp only [CollatzResearch.WordTrace]
  refine ⟨15030631226028687434144963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10020420817352458289429975 15030631226028687434144963)
  ·
    refine ⟨22545946839043031151217445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15030631226028687434144963 22545946839043031151217445)
    ·
      refine ⟨4227365032320568340853271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22545946839043031151217445 4227365032320568340853271)
      ·
        refine ⟨6341047548480852511279907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227365032320568340853271 6341047548480852511279907)
        ·
          refine ⟨9511571322721278766919861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341047548480852511279907 9511571322721278766919861)
          ·
            refine ⟨891709811505119884398737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9511571322721278766919861 891709811505119884398737)
            ·
              refine ⟨668782358628839913299053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891709811505119884398737 668782358628839913299053)
              ·
                refine ⟨250793384485814967487145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 668782358628839913299053 250793384485814967487145)
                ·
                  refine ⟨188095038364361225615359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250793384485814967487145 188095038364361225615359)
                  ·
                    rfl

theorem cell20_412103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 2].length) (baseStart_412103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412103 prefixEnd_412103 := by exact prefixLift 412103
  have htrace : WordTrace (prefixWord ++ tailWord_412103) baseStart_412103 baseEnd_412103 := by
    simpa [prefixWord, tailWord_412103, baseEnd_412103] using wordTrace_append hprefix tailTrace_412103
  have hstable : (prefixWord ++ tailWord_412103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412103).length < 2 ^ (prefixWord ++ tailWord_412103).sum := by decide
  have hdescent : baseEnd_412103 < baseStart_412103 := by decide
  rcases family_descends (prefixWord ++ tailWord_412103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412117 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_412117 : Nat := 118140960795 + 412117 * 2 ^ 59
def prefixEnd_412117 : Nat := 4983230072969 + 3 ^ 40 * 412117 * 2
def baseEnd_412117 : Nat := 188101428345839399148635

theorem tailTrace_412117 : CollatzResearch.WordTrace tailWord_412117 prefixEnd_412117 188101428345839399148635 := by
  unfold tailWord_412117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15031141847977967825154605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10020761231985311883436403 15031141847977967825154605)
  ·
    refine ⟨5636678192991737934432977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15031141847977967825154605 5636678192991737934432977)
    ·
      refine ⟨4227508644743803450824733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5636678192991737934432977 4227508644743803450824733)
      ·
        refine ⟨1585315741778926294059275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4227508644743803450824733 1585315741778926294059275)
        ·
          refine ⟨2377973612668389441088913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585315741778926294059275 2377973612668389441088913)
          ·
            refine ⟨1783480209501292080816685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2377973612668389441088913 1783480209501292080816685)
            ·
              refine ⟨668805078562984530306257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1783480209501292080816685 668805078562984530306257)
              ·
                refine ⟨501603808922238397729693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668805078562984530306257 501603808922238397729693)
                ·
                  refine ⟨188101428345839399148635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501603808922238397729693 188101428345839399148635)
                  ·
                    rfl

theorem cell20_412117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_412117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412117 prefixEnd_412117 := by exact prefixLift 412117
  have htrace : WordTrace (prefixWord ++ tailWord_412117) baseStart_412117 baseEnd_412117 := by
    simpa [prefixWord, tailWord_412117, baseEnd_412117] using wordTrace_append hprefix tailTrace_412117
  have hstable : (prefixWord ++ tailWord_412117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412117).length < 2 ^ (prefixWord ++ tailWord_412117).sum := by decide
  have hdescent : baseEnd_412117 < baseStart_412117 := by decide
  rcases family_descends (prefixWord ++ tailWord_412117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412130 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_412130 : Nat := 118140960795 + 412130 * 2 ^ 59
def prefixEnd_412130 : Nat := 4983230072969 + 3 ^ 40 * 412130 * 2
def baseEnd_412130 : Nat := 188107361900069131715249

theorem tailTrace_412130 : CollatzResearch.WordTrace tailWord_412130 prefixEnd_412130 188107361900069131715249 := by
  unfold tailWord_412130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757903999232717761344461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10021077331287247363585229 3757903999232717761344461)
  ·
    refine ⟨1409213999712269160504173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3757903999232717761344461 1409213999712269160504173)
    ·
      refine ⟨528455249892100935189065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1409213999712269160504173 528455249892100935189065)
      ·
        refine ⟨396341437419075701391799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528455249892100935189065 396341437419075701391799)
        ·
          refine ⟨594512156128613552087699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396341437419075701391799 594512156128613552087699)
          ·
            refine ⟨891768234192920328131549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594512156128613552087699 891768234192920328131549)
            ·
              refine ⟨334413087822345123049331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891768234192920328131549 334413087822345123049331)
              ·
                refine ⟨501619631733517684573997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334413087822345123049331 501619631733517684573997)
                ·
                  refine ⟨188107361900069131715249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501619631733517684573997 188107361900069131715249)
                  ·
                    rfl

theorem cell20_412130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_412130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412130 prefixEnd_412130 := by exact prefixLift 412130
  have htrace : WordTrace (prefixWord ++ tailWord_412130) baseStart_412130 baseEnd_412130 := by
    simpa [prefixWord, tailWord_412130, baseEnd_412130] using wordTrace_append hprefix tailTrace_412130
  have hstable : (prefixWord ++ tailWord_412130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412130).length < 2 ^ (prefixWord ++ tailWord_412130).sum := by decide
  have hdescent : baseEnd_412130 < baseStart_412130 := by decide
  rcases family_descends (prefixWord ++ tailWord_412130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412145 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_412145 : Nat := 118140960795 + 412145 * 2 ^ 59
def prefixEnd_412145 : Nat := 4983230072969 + 3 ^ 40 * 412145 * 2
def baseEnd_412145 : Nat := 188114208308795746215187

theorem tailTrace_412145 : CollatzResearch.WordTrace tailWord_412145 prefixEnd_412145 188114208308795746215187 := by
  unfold tailWord_412145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15032163091876528607173889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10021442061251019071449259 15032163091876528607173889)
  ·
    refine ⟨11274122318907396455380417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15032163091876528607173889 11274122318907396455380417)
    ·
      refine ⟨8455591739180547341535313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11274122318907396455380417 8455591739180547341535313)
      ·
        refine ⟨6341693804385410506151485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8455591739180547341535313 6341693804385410506151485)
        ·
          refine ⟨2378135176644528939806807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6341693804385410506151485 2378135176644528939806807)
          ·
            refine ⟨3567202764966793409710211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378135176644528939806807 3567202764966793409710211)
            ·
              refine ⟨5350804147450190114565317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567202764966793409710211 5350804147450190114565317)
              ·
                refine ⟨1003275777646910646480997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5350804147450190114565317 1003275777646910646480997)
                ·
                  refine ⟨188114208308795746215187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003275777646910646480997 188114208308795746215187)
                  ·
                    rfl

theorem cell20_412145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_412145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412145 prefixEnd_412145 := by exact prefixLift 412145
  have htrace : WordTrace (prefixWord ++ tailWord_412145) baseStart_412145 baseEnd_412145 := by
    simpa [prefixWord, tailWord_412145, baseEnd_412145] using wordTrace_append hprefix tailTrace_412145
  have hstable : (prefixWord ++ tailWord_412145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412145).length < 2 ^ (prefixWord ++ tailWord_412145).sum := by decide
  have hdescent : baseEnd_412145 < baseStart_412145 := by decide
  rcases family_descends (prefixWord ++ tailWord_412145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412152 : List Nat := [2, 1, 2, 1, 1, 4, 3, 6]
def baseStart_412152 : Nat := 118140960795 + 412152 * 2 ^ 59
def prefixEnd_412152 : Nat := 4983230072969 + 3 ^ 40 * 412152 * 2
def baseEnd_412152 : Nat := 62705801099844944327275

theorem tailTrace_412152 : CollatzResearch.WordTrace tailWord_412152 prefixEnd_412152 62705801099844944327275 := by
  unfold tailWord_412152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7516209201425584401339355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10021612268567445868452473 7516209201425584401339355)
  ·
    refine ⟨11274313802138376602009033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7516209201425584401339355 11274313802138376602009033)
    ·
      refine ⟨8455735351603782451506775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11274313802138376602009033 8455735351603782451506775)
      ·
        refine ⟨12683603027405673677260163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8455735351603782451506775 12683603027405673677260163)
        ·
          refine ⟨19025404541108510515890245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12683603027405673677260163 19025404541108510515890245)
          ·
            refine ⟨3567263351457845721729421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19025404541108510515890245 3567263351457845721729421)
            ·
              refine ⟨1337723756796692145648533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3567263351457845721729421 1337723756796692145648533)
              ·
                refine ⟨62705801099844944327275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1337723756796692145648533 62705801099844944327275)
                ·
                  rfl

theorem cell20_412152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_412152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412152 prefixEnd_412152 := by exact prefixLift 412152
  have htrace : WordTrace (prefixWord ++ tailWord_412152) baseStart_412152 baseEnd_412152 := by
    simpa [prefixWord, tailWord_412152, baseEnd_412152] using wordTrace_append hprefix tailTrace_412152
  have hstable : (prefixWord ++ tailWord_412152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412152).length < 2 ^ (prefixWord ++ tailWord_412152).sum := by decide
  have hdescent : baseEnd_412152 < baseStart_412152 := by decide
  rcases family_descends (prefixWord ++ tailWord_412152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412159 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 7]
def baseStart_412159 : Nat := 118140960795 + 412159 * 2 ^ 59
def prefixEnd_412159 : Nat := 4983230072969 + 3 ^ 40 * 412159 * 2
def baseEnd_412159 : Nat := 188120598290273919748463

theorem tailTrace_412159 : CollatzResearch.WordTrace tailWord_412159 prefixEnd_412159 188120598290273919748463 := by
  unfold tailWord_412159
  simp only [CollatzResearch.WordTrace]
  refine ⟨15032673713825808998183531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10021782475883872665455687 15032673713825808998183531)
  ·
    refine ⟨22549010570738713497275297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15032673713825808998183531 22549010570738713497275297)
    ·
      refine ⟨16911757928054035122956473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22549010570738713497275297 16911757928054035122956473)
      ·
        refine ⟨12683818446040526342217355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16911757928054035122956473 12683818446040526342217355)
        ·
          refine ⟨19025727669060789513326033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12683818446040526342217355 19025727669060789513326033)
          ·
            refine ⟨14269295751795592134994525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19025727669060789513326033 14269295751795592134994525)
            ·
              refine ⟨5350985906923347050622947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14269295751795592134994525 5350985906923347050622947)
              ·
                refine ⟨8026478860385020575934421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350985906923347050622947 8026478860385020575934421)
                ·
                  refine ⟨188120598290273919748463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8026478860385020575934421 188120598290273919748463)
                  ·
                    rfl

theorem cell20_412159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_412159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412159 prefixEnd_412159 := by exact prefixLift 412159
  have htrace : WordTrace (prefixWord ++ tailWord_412159) baseStart_412159 baseEnd_412159 := by
    simpa [prefixWord, tailWord_412159, baseEnd_412159] using wordTrace_append hprefix tailTrace_412159
  have hstable : (prefixWord ++ tailWord_412159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412159).length < 2 ^ (prefixWord ++ tailWord_412159).sum := by decide
  have hdescent : baseEnd_412159 < baseStart_412159 := by decide
  rcases family_descends (prefixWord ++ tailWord_412159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412179 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 2]
def baseStart_412179 : Nat := 118140960795 + 412179 * 2 ^ 59
def prefixEnd_412179 : Nat := 4983230072969 + 3 ^ 40 * 412179 * 2
def baseEnd_412179 : Nat := 188129726835242739081715

theorem tailTrace_412179 : CollatzResearch.WordTrace tailWord_412179 prefixEnd_412179 188129726835242739081715 := by
  unfold tailWord_412179
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033403173753352413911591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10022268782502234942607727 15033403173753352413911591)
  ·
    refine ⟨22550104760630028620867387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15033403173753352413911591 22550104760630028620867387)
    ·
      refine ⟨33825157140945042931301081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22550104760630028620867387 33825157140945042931301081)
      ·
        refine ⟨25368867855708782198475811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33825157140945042931301081 25368867855708782198475811)
        ·
          refine ⟨38053301783563173297713717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25368867855708782198475811 38053301783563173297713717)
          ·
            refine ⟨3567497042209047496660661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38053301783563173297713717 3567497042209047496660661)
            ·
              refine ⟨334452847707098202811937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3567497042209047496660661 334452847707098202811937)
              ·
                refine ⟨250839635780323652108953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334452847707098202811937 250839635780323652108953)
                ·
                  refine ⟨188129726835242739081715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250839635780323652108953 188129726835242739081715)
                  ·
                    rfl

theorem cell20_412179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 2].length) (baseStart_412179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412179 prefixEnd_412179 := by exact prefixLift 412179
  have htrace : WordTrace (prefixWord ++ tailWord_412179) baseStart_412179 baseEnd_412179 := by
    simpa [prefixWord, tailWord_412179, baseEnd_412179] using wordTrace_append hprefix tailTrace_412179
  have hstable : (prefixWord ++ tailWord_412179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412179).length < 2 ^ (prefixWord ++ tailWord_412179).sum := by decide
  have hdescent : baseEnd_412179 < baseStart_412179 := by decide
  rcases family_descends (prefixWord ++ tailWord_412179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412230 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_412230 : Nat := 118140960795 + 412230 * 2 ^ 59
def prefixEnd_412230 : Nat := 4983230072969 + 3 ^ 40 * 412230 * 2
def baseEnd_412230 : Nat := 188153004624913228381507

theorem tailTrace_412230 : CollatzResearch.WordTrace tailWord_412230 prefixEnd_412230 188153004624913228381507 := by
  unfold tailWord_412230
  simp only [CollatzResearch.WordTrace]
  refine ⟨469851978017768378875567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10023508864379058749345429 469851978017768378875567)
  ·
    refine ⟨704777967026652568313351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469851978017768378875567 704777967026652568313351)
    ·
      refine ⟨1057166950539978852470027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704777967026652568313351 1057166950539978852470027)
      ·
        refine ⟨1585750425809968278705041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057166950539978852470027 1585750425809968278705041)
        ·
          refine ⟨1189312819357476209028781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1585750425809968278705041 1189312819357476209028781)
          ·
            refine ⟨445992307259053578385793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1189312819357476209028781 445992307259053578385793)
            ·
              refine ⟨334494230444290183789345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445992307259053578385793 334494230444290183789345)
              ·
                refine ⟨250870672833217637842009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334494230444290183789345 250870672833217637842009)
                ·
                  refine ⟨188153004624913228381507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250870672833217637842009 188153004624913228381507)
                  ·
                    rfl

theorem cell20_412230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_412230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412230 prefixEnd_412230 := by exact prefixLift 412230
  have htrace : WordTrace (prefixWord ++ tailWord_412230) baseStart_412230 baseEnd_412230 := by
    simpa [prefixWord, tailWord_412230, baseEnd_412230] using wordTrace_append hprefix tailTrace_412230
  have hstable : (prefixWord ++ tailWord_412230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412230).length < 2 ^ (prefixWord ++ tailWord_412230).sum := by decide
  have hdescent : baseEnd_412230 < baseStart_412230 := by decide
  rcases family_descends (prefixWord ++ tailWord_412230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412231 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 3]
def baseStart_412231 : Nat := 118140960795 + 412231 * 2 ^ 59
def prefixEnd_412231 : Nat := 4983230072969 + 3 ^ 40 * 412231 * 2
def baseEnd_412231 : Nat := 188153461052161669348169

theorem tailTrace_412231 : CollatzResearch.WordTrace tailWord_412231 prefixEnd_412231 188153461052161669348169 := by
  unfold tailWord_412231
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035299769564965294804547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10023533179709976863203031 15035299769564965294804547)
  ·
    refine ⟨22552949654347447942206821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15035299769564965294804547 22552949654347447942206821)
    ·
      refine ⟨4228678060190146489163779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22552949654347447942206821 4228678060190146489163779)
      ·
        refine ⟨6343017090285219733745669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228678060190146489163779 6343017090285219733745669)
        ·
          refine ⟨1189315704428478700077313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6343017090285219733745669 1189315704428478700077313)
          ·
            refine ⟨891986778321359025057985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189315704428478700077313 891986778321359025057985)
            ·
              refine ⟨668990083741019268793489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891986778321359025057985 668990083741019268793489)
              ·
                refine ⟨501742562805764451595117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668990083741019268793489 501742562805764451595117)
                ·
                  refine ⟨188153461052161669348169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501742562805764451595117 188153461052161669348169)
                  ·
                    rfl

theorem cell20_412231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 3].length) (baseStart_412231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412231 prefixEnd_412231 := by exact prefixLift 412231
  have htrace : WordTrace (prefixWord ++ tailWord_412231) baseStart_412231 baseEnd_412231 := by
    simpa [prefixWord, tailWord_412231, baseEnd_412231] using wordTrace_append hprefix tailTrace_412231
  have hstable : (prefixWord ++ tailWord_412231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412231).length < 2 ^ (prefixWord ++ tailWord_412231).sum := by decide
  have hdescent : baseEnd_412231 < baseStart_412231 := by decide
  rcases family_descends (prefixWord ++ tailWord_412231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412234 : List Nat := [3, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_412234 : Nat := 118140960795 + 412234 * 2 ^ 59
def prefixEnd_412234 : Nat := 4983230072969 + 3 ^ 40 * 412234 * 2
def baseEnd_412234 : Nat := 188154830333906992248157

theorem tailTrace_412234 : CollatzResearch.WordTrace tailWord_412234 prefixEnd_412234 188154830333906992248157 := by
  unfold tailWord_412234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758852297138524201790939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10023606125702731204775837 3758852297138524201790939)
  ·
    refine ⟨5638278445707786302686409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3758852297138524201790939 5638278445707786302686409)
    ·
      refine ⟨4228708834280839727014807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5638278445707786302686409 4228708834280839727014807)
      ·
        refine ⟨6343063251421259590522211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228708834280839727014807 6343063251421259590522211)
        ·
          refine ⟨9514594877131889385783317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6343063251421259590522211 9514594877131889385783317)
          ·
            refine ⟨445996634865557314958593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9514594877131889385783317 445996634865557314958593)
            ·
              refine ⟨334497476149167986218945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445996634865557314958593 334497476149167986218945)
              ·
                refine ⟨250873107111875989664209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334497476149167986218945 250873107111875989664209)
                ·
                  refine ⟨188154830333906992248157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250873107111875989664209 188154830333906992248157)
                  ·
                    rfl

theorem cell20_412234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_412234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412234 prefixEnd_412234 := by exact prefixLift 412234
  have htrace : WordTrace (prefixWord ++ tailWord_412234) baseStart_412234 baseEnd_412234 := by
    simpa [prefixWord, tailWord_412234, baseEnd_412234] using wordTrace_append hprefix tailTrace_412234
  have hstable : (prefixWord ++ tailWord_412234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412234).length < 2 ^ (prefixWord ++ tailWord_412234).sum := by decide
  have hdescent : baseEnd_412234 < baseStart_412234 := by decide
  rcases family_descends (prefixWord ++ tailWord_412234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412235 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_412235 : Nat := 118140960795 + 412235 * 2 ^ 59
def prefixEnd_412235 : Nat := 4983230072969 + 3 ^ 40 * 412235 * 2
def baseEnd_412235 : Nat := 188155286761155433214819

theorem tailTrace_412235 : CollatzResearch.WordTrace tailWord_412235 prefixEnd_412235 188155286761155433214819 := by
  unfold tailWord_412235
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035445661550473977950159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10023630441033649318633439 15035445661550473977950159)
  ·
    refine ⟨22553168492325710966925239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15035445661550473977950159 22553168492325710966925239)
    ·
      refine ⟨33829752738488566450387859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22553168492325710966925239 33829752738488566450387859)
      ·
        refine ⟨50744629107732849675581789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33829752738488566450387859 50744629107732849675581789)
        ·
          refine ⟨19029235915399818628343171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50744629107732849675581789 19029235915399818628343171)
          ·
            refine ⟨28543853873099727942514757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19029235915399818628343171 28543853873099727942514757)
            ·
              refine ⟨5351972601206198989221517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28543853873099727942514757 5351972601206198989221517)
              ·
                refine ⟨2006989725452324620958069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5351972601206198989221517 2006989725452324620958069)
                ·
                  refine ⟨188155286761155433214819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2006989725452324620958069 188155286761155433214819)
                  ·
                    rfl

theorem cell20_412235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_412235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412235 prefixEnd_412235 := by exact prefixLift 412235
  have htrace : WordTrace (prefixWord ++ tailWord_412235) baseStart_412235 baseEnd_412235 := by
    simpa [prefixWord, tailWord_412235, baseEnd_412235] using wordTrace_append hprefix tailTrace_412235
  have hstable : (prefixWord ++ tailWord_412235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412235).length < 2 ^ (prefixWord ++ tailWord_412235).sum := by decide
  have hdescent : baseEnd_412235 < baseStart_412235 := by decide
  rcases family_descends (prefixWord ++ tailWord_412235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412259 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_412259 : Nat := 118140960795 + 412259 * 2 ^ 59
def prefixEnd_412259 : Nat := 4983230072969 + 3 ^ 40 * 412259 * 2
def baseEnd_412259 : Nat := 188166241015118016414721

theorem tailTrace_412259 : CollatzResearch.WordTrace tailWord_412259 prefixEnd_412259 188166241015118016414721 := by
  unfold tailWord_412259
  simp only [CollatzResearch.WordTrace]
  refine ⟨15036321013463526076823831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10024214008975684051215887 15036321013463526076823831)
  ·
    refine ⟨22554481520195289115235747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15036321013463526076823831 22554481520195289115235747)
    ·
      refine ⟨33831722280292933672853621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22554481520195289115235747 33831722280292933672853621)
      ·
        refine ⟨3171723963777462531830027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33831722280292933672853621 3171723963777462531830027)
        ·
          refine ⟨4757585945666193797745041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171723963777462531830027 4757585945666193797745041)
          ·
            refine ⟨3568189459249645348308781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4757585945666193797745041 3568189459249645348308781)
            ·
              refine ⟨1338071047218617005615793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3568189459249645348308781 1338071047218617005615793)
              ·
                refine ⟨1003553285413962754211845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338071047218617005615793 1003553285413962754211845)
                ·
                  refine ⟨188166241015118016414721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003553285413962754211845 188166241015118016414721)
                  ·
                    rfl

theorem cell20_412259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_412259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412259 prefixEnd_412259 := by exact prefixLift 412259
  have htrace : WordTrace (prefixWord ++ tailWord_412259) baseStart_412259 baseEnd_412259 := by
    simpa [prefixWord, tailWord_412259, baseEnd_412259] using wordTrace_append hprefix tailTrace_412259
  have hstable : (prefixWord ++ tailWord_412259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412259).length < 2 ^ (prefixWord ++ tailWord_412259).sum := by decide
  have hdescent : baseEnd_412259 < baseStart_412259 := by decide
  rcases family_descends (prefixWord ++ tailWord_412259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412321 : List Nat := [1, 2, 3, 3, 3, 1, 1, 6]
def baseStart_412321 : Nat := 118140960795 + 412321 * 2 ^ 59
def prefixEnd_412321 : Nat := 4983230072969 + 3 ^ 40 * 412321 * 2
def baseEnd_412321 : Nat := 62731513168173785449267

theorem tailTrace_412321 : CollatzResearch.WordTrace tailWord_412321 prefixEnd_412321 62731513168173785449267 := by
  unfold tailWord_412321
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038582339238910665580817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10025721559492607110387211 15038582339238910665580817)
  ·
    refine ⟨11278936754429182999185613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15038582339238910665580817 11278936754429182999185613)
    ·
      refine ⟨4229601282910943624694605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11278936754429182999185613 4229601282910943624694605)
      ·
        refine ⟨1586100481091603859260477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4229601282910943624694605 1586100481091603859260477)
        ·
          refine ⟨594787680409351447222679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1586100481091603859260477 594787680409351447222679)
          ·
            refine ⟨892181520614027170834019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594787680409351447222679 892181520614027170834019)
            ·
              refine ⟨1338272280921040756251029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892181520614027170834019 1338272280921040756251029)
              ·
                refine ⟨62731513168173785449267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1338272280921040756251029 62731513168173785449267)
                ·
                  rfl

theorem cell20_412321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_412321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412321 prefixEnd_412321 := by exact prefixLift 412321
  have htrace : WordTrace (prefixWord ++ tailWord_412321) baseStart_412321 baseEnd_412321 := by
    simpa [prefixWord, tailWord_412321, baseEnd_412321] using wordTrace_append hprefix tailTrace_412321
  have hstable : (prefixWord ++ tailWord_412321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412321).length < 2 ^ (prefixWord ++ tailWord_412321).sum := by decide
  have hdescent : baseEnd_412321 < baseStart_412321 := by decide
  rcases family_descends (prefixWord ++ tailWord_412321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412327 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 2]
def baseStart_412327 : Nat := 118140960795 + 412327 * 2 ^ 59
def prefixEnd_412327 : Nat := 4983230072969 + 3 ^ 40 * 412327 * 2
def baseEnd_412327 : Nat := 188197278068012002147777

theorem tailTrace_412327 : CollatzResearch.WordTrace tailWord_412327 prefixEnd_412327 188197278068012002147777 := by
  unfold tailWord_412327
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038801177217173690299235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10025867451478115793532823 15038801177217173690299235)
  ·
    refine ⟨22558201765825760535448853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15038801177217173690299235 22558201765825760535448853)
    ·
      refine ⟨1057415707773082525099165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22558201765825760535448853 1057415707773082525099165)
      ·
        refine ⟨396530890414905946912187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1057415707773082525099165 396530890414905946912187)
        ·
          refine ⟨594796335622358920368281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396530890414905946912187 594796335622358920368281)
          ·
            refine ⟨446097251716769190276211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594796335622358920368281 446097251716769190276211)
            ·
              refine ⟨669145877575153785414317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446097251716769190276211 669145877575153785414317)
              ·
                refine ⟨250929704090682669530369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669145877575153785414317 250929704090682669530369)
                ·
                  refine ⟨188197278068012002147777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250929704090682669530369 188197278068012002147777)
                  ·
                    rfl

theorem cell20_412327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 2].length) (baseStart_412327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412327 prefixEnd_412327 := by exact prefixLift 412327
  have htrace : WordTrace (prefixWord ++ tailWord_412327) baseStart_412327 baseEnd_412327 := by
    simpa [prefixWord, tailWord_412327, baseEnd_412327] using wordTrace_append hprefix tailTrace_412327
  have hstable : (prefixWord ++ tailWord_412327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412327).length < 2 ^ (prefixWord ++ tailWord_412327).sum := by decide
  have hdescent : baseEnd_412327 < baseStart_412327 := by decide
  rcases family_descends (prefixWord ++ tailWord_412327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412352 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_412352 : Nat := 118140960795 + 412352 * 2 ^ 59
def prefixEnd_412352 : Nat := 4983230072969 + 3 ^ 40 * 412352 * 2
def baseEnd_412352 : Nat := 188208688749223026314341

theorem tailTrace_412352 : CollatzResearch.WordTrace tailWord_412352 prefixEnd_412352 188208688749223026314341 := by
  unfold tailWord_412352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519856501063301479979655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10026475334751068639972873 7519856501063301479979655)
  ·
    refine ⟨11279784751594952219969483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7519856501063301479979655 11279784751594952219969483)
    ·
      refine ⟨16919677127392428329954225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279784751594952219969483 16919677127392428329954225)
      ·
        refine ⟨12689757845544321247465669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16919677127392428329954225 12689757845544321247465669)
        ·
          refine ⟨2379329596039560233899813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12689757845544321247465669 2379329596039560233899813)
          ·
            refine ⟨446124299257417543856215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2379329596039560233899813 446124299257417543856215)
            ·
              refine ⟨669186448886126315784323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446124299257417543856215 669186448886126315784323)
              ·
                refine ⟨1003779673329189473676485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669186448886126315784323 1003779673329189473676485)
                ·
                  refine ⟨188208688749223026314341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003779673329189473676485 188208688749223026314341)
                  ·
                    rfl

theorem cell20_412352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_412352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412352 prefixEnd_412352 := by exact prefixLift 412352
  have htrace : WordTrace (prefixWord ++ tailWord_412352) baseStart_412352 baseEnd_412352 := by
    simpa [prefixWord, tailWord_412352, baseEnd_412352] using wordTrace_append hprefix tailTrace_412352
  have hstable : (prefixWord ++ tailWord_412352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412352).length < 2 ^ (prefixWord ++ tailWord_412352).sum := by decide
  have hdescent : baseEnd_412352 < baseStart_412352 := by decide
  rcases family_descends (prefixWord ++ tailWord_412352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412362 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_412362 : Nat := 118140960795 + 412362 * 2 ^ 59
def prefixEnd_412362 : Nat := 4983230072969 + 3 ^ 40 * 412362 * 2
def baseEnd_412362 : Nat := 188213253021707435980967

theorem tailTrace_412362 : CollatzResearch.WordTrace tailWord_412362 prefixEnd_412362 188213253021707435980967 := by
  unfold tailWord_412362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760019433022593666955835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10026718488060249778548893 3760019433022593666955835)
  ·
    refine ⟨5640029149533890500433753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760019433022593666955835 5640029149533890500433753)
    ·
      refine ⟨4230021862150417875325315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5640029149533890500433753 4230021862150417875325315)
      ·
        refine ⟨6345032793225626812987973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230021862150417875325315 6345032793225626812987973)
        ·
          refine ⟨1189693648729805027435245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6345032793225626812987973 1189693648729805027435245)
          ·
            refine ⟨446135118273676885288217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1189693648729805027435245 446135118273676885288217)
            ·
              refine ⟨334601338705257663966163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446135118273676885288217 334601338705257663966163)
              ·
                refine ⟨501902008057886495949245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334601338705257663966163 501902008057886495949245)
                ·
                  refine ⟨188213253021707435980967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501902008057886495949245 188213253021707435980967)
                  ·
                    rfl

theorem cell20_412362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_412362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412362 prefixEnd_412362 := by exact prefixLift 412362
  have htrace : WordTrace (prefixWord ++ tailWord_412362) baseStart_412362 baseEnd_412362 := by
    simpa [prefixWord, tailWord_412362, baseEnd_412362] using wordTrace_append hprefix tailTrace_412362
  have hstable : (prefixWord ++ tailWord_412362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412362).length < 2 ^ (prefixWord ++ tailWord_412362).sum := by decide
  have hdescent : baseEnd_412362 < baseStart_412362 := by decide
  rcases family_descends (prefixWord ++ tailWord_412362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412414 : List Nat := [4, 2, 2, 1, 2, 3, 1, 5]
def baseStart_412414 : Nat := 118140960795 + 412414 * 2 ^ 59
def prefixEnd_412414 : Nat := 4983230072969 + 3 ^ 40 * 412414 * 2
def baseEnd_412414 : Nat := 62745662412875455415807

theorem tailTrace_412414 : CollatzResearch.WordTrace tailWord_412414 prefixEnd_412414 62745662412875455415807 := by
  unfold tailWord_412414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880246790987748443589537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10027982885267991699144197 1880246790987748443589537)
  ·
    refine ⟨1410185093240811332692153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1880246790987748443589537 1410185093240811332692153)
    ·
      refine ⟨1057638819930608499519115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1410185093240811332692153 1057638819930608499519115)
      ·
        refine ⟨1586458229895912749278673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057638819930608499519115 1586458229895912749278673)
        ·
          refine ⟨1189843672421934561959005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586458229895912749278673 1189843672421934561959005)
          ·
            refine ⟨446191377158225460734627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1189843672421934561959005 446191377158225460734627)
            ·
              refine ⟨669287065737338191101941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446191377158225460734627 669287065737338191101941)
              ·
                refine ⟨62745662412875455415807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 669287065737338191101941 62745662412875455415807)
                ·
                  rfl

theorem cell20_412414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_412414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412414 prefixEnd_412414 := by exact prefixLift 412414
  have htrace : WordTrace (prefixWord ++ tailWord_412414) baseStart_412414 baseEnd_412414 := by
    simpa [prefixWord, tailWord_412414, baseEnd_412414] using wordTrace_append hprefix tailTrace_412414
  have hstable : (prefixWord ++ tailWord_412414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412414).length < 2 ^ (prefixWord ++ tailWord_412414).sum := by decide
  have hdescent : baseEnd_412414 < baseStart_412414 := by decide
  rcases family_descends (prefixWord ++ tailWord_412414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412456 : List Nat := [2, 1, 5, 1, 1, 1, 9]
def baseStart_412456 : Nat := 118140960795 + 412456 * 2 ^ 59
def prefixEnd_412456 : Nat := 4983230072969 + 3 ^ 40 * 412456 * 2
def baseEnd_412456 : Nat := 20917350798117876316361

theorem tailTrace_412456 : CollatzResearch.WordTrace tailWord_412456 prefixEnd_412456 20917350798117876316361 := by
  unfold tailWord_412456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521753096874914360872611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10029004129166552481163481 7521753096874914360872611)
  ·
    refine ⟨11282629645312371541308917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521753096874914360872611 11282629645312371541308917)
    ·
      refine ⟨1057746529248034831997711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11282629645312371541308917 1057746529248034831997711)
      ·
        refine ⟨1586619793872052247996567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057746529248034831997711 1586619793872052247996567)
        ·
          refine ⟨2379929690808078371994851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586619793872052247996567 2379929690808078371994851)
          ·
            refine ⟨3569894536212117557992277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379929690808078371994851 3569894536212117557992277)
            ·
              refine ⟨20917350798117876316361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3569894536212117557992277 20917350798117876316361)
              ·
                rfl

theorem cell20_412456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_412456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412456 prefixEnd_412456 := by exact prefixLift 412456
  have htrace : WordTrace (prefixWord ++ tailWord_412456) baseStart_412456 baseEnd_412456 := by
    simpa [prefixWord, tailWord_412456, baseEnd_412456] using wordTrace_append hprefix tailTrace_412456
  have hstable : (prefixWord ++ tailWord_412456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412456).length < 2 ^ (prefixWord ++ tailWord_412456).sum := by decide
  have hdescent : baseEnd_412456 < baseStart_412456 := by decide
  rcases family_descends (prefixWord ++ tailWord_412456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412466 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_412466 : Nat := 118140960795 + 412466 * 2 ^ 59
def prefixEnd_412466 : Nat := 4983230072969 + 3 ^ 40 * 412466 * 2
def baseEnd_412466 : Nat := 188260721455545296513875

theorem tailTrace_412466 : CollatzResearch.WordTrace tailWord_412466 prefixEnd_412466 188260721455545296513875 := by
  unfold tailWord_412466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760967730928400107402313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10029247282475733619739501 3760967730928400107402313)
  ·
    refine ⟨2820725798196300080551735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3760967730928400107402313 2820725798196300080551735)
    ·
      refine ⟨4231088697294450120827603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820725798196300080551735 4231088697294450120827603)
      ·
        refine ⟨6346633045941675181241405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231088697294450120827603 6346633045941675181241405)
        ·
          refine ⟨2379987392228128192965527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6346633045941675181241405 2379987392228128192965527)
          ·
            refine ⟨3569981088342192289448291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379987392228128192965527 3569981088342192289448291)
            ·
              refine ⟨5354971632513288434172437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569981088342192289448291 5354971632513288434172437)
              ·
                refine ⟨251014295274060395351833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5354971632513288434172437 251014295274060395351833)
                ·
                  refine ⟨188260721455545296513875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251014295274060395351833 188260721455545296513875)
                  ·
                    rfl

theorem cell20_412466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_412466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412466 prefixEnd_412466 := by exact prefixLift 412466
  have htrace : WordTrace (prefixWord ++ tailWord_412466) baseStart_412466 baseEnd_412466 := by
    simpa [prefixWord, tailWord_412466, baseEnd_412466] using wordTrace_append hprefix tailTrace_412466
  have hstable : (prefixWord ++ tailWord_412466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412466).length < 2 ^ (prefixWord ++ tailWord_412466).sum := by decide
  have hdescent : baseEnd_412466 < baseStart_412466 := by decide
  rcases family_descends (prefixWord ++ tailWord_412466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412486 : List Nat := [6, 1, 1, 2, 2, 2, 2, 4]
def baseStart_412486 : Nat := 118140960795 + 412486 * 2 ^ 59
def prefixEnd_412486 : Nat := 4983230072969 + 3 ^ 40 * 412486 * 2
def baseEnd_412486 : Nat := 62756616666838038615709

theorem tailTrace_412486 : CollatzResearch.WordTrace tailWord_412486 prefixEnd_412486 62756616666838038615709 := by
  unfold tailWord_412486
  simp only [CollatzResearch.WordTrace]
  refine ⟨470143761988785745166791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10029733589094095896891541 470143761988785745166791)
  ·
    refine ⟨705215642983178617750187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470143761988785745166791 705215642983178617750187)
    ·
      refine ⟨1057823464474767926625281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705215642983178617750187 1057823464474767926625281)
      ·
        refine ⟨793367598356075944968961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1057823464474767926625281 793367598356075944968961)
        ·
          refine ⟨595025698767056958726721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793367598356075944968961 595025698767056958726721)
          ·
            refine ⟨446269274075292719045041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595025698767056958726721 446269274075292719045041)
            ·
              refine ⟨334701955556469539283781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446269274075292719045041 334701955556469539283781)
              ·
                refine ⟨62756616666838038615709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334701955556469539283781 62756616666838038615709)
                ·
                  rfl

theorem cell20_412486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_412486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412486 prefixEnd_412486 := by exact prefixLift 412486
  have htrace : WordTrace (prefixWord ++ tailWord_412486) baseStart_412486 baseEnd_412486 := by
    simpa [prefixWord, tailWord_412486, baseEnd_412486] using wordTrace_append hprefix tailTrace_412486
  have hstable : (prefixWord ++ tailWord_412486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412486).length < 2 ^ (prefixWord ++ tailWord_412486).sum := by decide
  have hdescent : baseEnd_412486 < baseStart_412486 := by decide
  rcases family_descends (prefixWord ++ tailWord_412486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412500 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 2]
def baseStart_412500 : Nat := 118140960795 + 412500 * 2 ^ 59
def prefixEnd_412500 : Nat := 4983230072969 + 3 ^ 40 * 412500 * 2
def baseEnd_412500 : Nat := 188276239981992289380403

theorem tailTrace_412500 : CollatzResearch.WordTrace tailWord_412500 prefixEnd_412500 188276239981992289380403 := by
  unfold tailWord_412500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522555502795212118173477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10030074003726949490897969 7522555502795212118173477)
  ·
    refine ⟨1410479156774102272157527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7522555502795212118173477 1410479156774102272157527)
    ·
      refine ⟨2115718735161153408236291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410479156774102272157527 2115718735161153408236291)
      ·
        refine ⟨3173578102741730112354437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115718735161153408236291 3173578102741730112354437)
        ·
          refine ⟨595045894264074396066457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3173578102741730112354437 595045894264074396066457)
          ·
            refine ⟨446284420698055797049843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595045894264074396066457 446284420698055797049843)
            ·
              refine ⟨669426631047083695574765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446284420698055797049843 669426631047083695574765)
              ·
                refine ⟨251034986642656385840537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669426631047083695574765 251034986642656385840537)
                ·
                  refine ⟨188276239981992289380403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251034986642656385840537 188276239981992289380403)
                  ·
                    rfl

theorem cell20_412500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_412500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412500 prefixEnd_412500 := by exact prefixLift 412500
  have htrace : WordTrace (prefixWord ++ tailWord_412500) baseStart_412500 baseEnd_412500 := by
    simpa [prefixWord, tailWord_412500, baseEnd_412500] using wordTrace_append hprefix tailTrace_412500
  have hstable : (prefixWord ++ tailWord_412500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412500).length < 2 ^ (prefixWord ++ tailWord_412500).sum := by decide
  have hdescent : baseEnd_412500 < baseStart_412500 := by decide
  rcases family_descends (prefixWord ++ tailWord_412500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412501 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_412501 : Nat := 118140960795 + 412501 * 2 ^ 59
def prefixEnd_412501 : Nat := 4983230072969 + 3 ^ 40 * 412501 * 2
def baseEnd_412501 : Nat := 188276696409240730347065

theorem tailTrace_412501 : CollatzResearch.WordTrace tailWord_412501 prefixEnd_412501 188276696409240730347065 := by
  unfold tailWord_412501
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045147478586801407133357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10030098319057867604755571 15045147478586801407133357)
  ·
    refine ⟨5641930304470050527675009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15045147478586801407133357 5641930304470050527675009)
    ·
      refine ⟨4231447728352537895756257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5641930304470050527675009 4231447728352537895756257)
      ·
        refine ⟨3173585796264403421817193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4231447728352537895756257 3173585796264403421817193)
        ·
          refine ⟨2380189347198302566362895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3173585796264403421817193 2380189347198302566362895)
          ·
            refine ⟨3570284020797453849544343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380189347198302566362895 3570284020797453849544343)
            ·
              refine ⟨5355426031196180774316515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570284020797453849544343 5355426031196180774316515)
              ·
                refine ⟨8033139046794271161474773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355426031196180774316515 8033139046794271161474773)
                ·
                  refine ⟨188276696409240730347065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8033139046794271161474773 188276696409240730347065)
                  ·
                    rfl

theorem cell20_412501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_412501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412501 prefixEnd_412501 := by exact prefixLift 412501
  have htrace : WordTrace (prefixWord ++ tailWord_412501) baseStart_412501 baseEnd_412501 := by
    simpa [prefixWord, tailWord_412501, baseEnd_412501] using wordTrace_append hprefix tailTrace_412501
  have hstable : (prefixWord ++ tailWord_412501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412501).length < 2 ^ (prefixWord ++ tailWord_412501).sum := by decide
  have hdescent : baseEnd_412501 < baseStart_412501 := by decide
  rcases family_descends (prefixWord ++ tailWord_412501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412566 : List Nat := [5, 3, 1, 1, 1, 9]
def baseStart_412566 : Nat := 118140960795 + 412566 * 2 ^ 59
def prefixEnd_412566 : Nat := 4983230072969 + 3 ^ 40 * 412566 * 2
def baseEnd_412566 : Nat := 6974309784458866414079

theorem tailTrace_412566 : CollatzResearch.WordTrace tailWord_412566 prefixEnd_412566 6974309784458866414079 := by
  unfold tailWord_412566
  simp only [CollatzResearch.WordTrace]
  refine ⟨940469888959457344265597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10031678815567545005499701 940469888959457344265597)
  ·
    refine ⟨352676208359796504099599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 940469888959457344265597 352676208359796504099599)
    ·
      refine ⟨529014312539694756149399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352676208359796504099599 529014312539694756149399)
      ·
        refine ⟨793521468809542134224099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529014312539694756149399 793521468809542134224099)
        ·
          refine ⟨1190282203214313201336149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793521468809542134224099 1190282203214313201336149)
          ·
            refine ⟨6974309784458866414079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1190282203214313201336149 6974309784458866414079)
            ·
              rfl

theorem cell20_412566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 9].length) (baseStart_412566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412566 prefixEnd_412566 := by exact prefixLift 412566
  have htrace : WordTrace (prefixWord ++ tailWord_412566) baseStart_412566 baseEnd_412566 := by
    simpa [prefixWord, tailWord_412566, baseEnd_412566] using wordTrace_append hprefix tailTrace_412566
  have hstable : (prefixWord ++ tailWord_412566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412566).length < 2 ^ (prefixWord ++ tailWord_412566).sum := by decide
  have hdescent : baseEnd_412566 < baseStart_412566 := by decide
  rcases family_descends (prefixWord ++ tailWord_412566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412570 : List Nat := [3, 1, 1, 4, 3, 8]
def baseStart_412570 : Nat := 118140960795 + 412570 * 2 ^ 59
def prefixEnd_412570 : Nat := 4983230072969 + 3 ^ 40 * 412570 * 2
def baseEnd_412570 : Nat := 6974377403310487298029

theorem tailTrace_412570 : CollatzResearch.WordTrace tailWord_412570 prefixEnd_412570 6974377403310487298029 := by
  unfold tailWord_412570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761916028834206547848791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10031776076891217460930109 3761916028834206547848791)
  ·
    refine ⟨5642874043251309821773187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3761916028834206547848791 5642874043251309821773187)
    ·
      refine ⟨8464311064876964732659781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5642874043251309821773187 8464311064876964732659781)
      ·
        refine ⟨1587058324664430887373709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8464311064876964732659781 1587058324664430887373709)
        ·
          refine ⟨595146871749161582765141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1587058324664430887373709 595146871749161582765141)
          ·
            refine ⟨6974377403310487298029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 595146871749161582765141 6974377403310487298029)
            ·
              rfl

theorem cell20_412570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 8].length) (baseStart_412570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412570 prefixEnd_412570 := by exact prefixLift 412570
  have htrace : WordTrace (prefixWord ++ tailWord_412570) baseStart_412570 baseEnd_412570 := by
    simpa [prefixWord, tailWord_412570, baseEnd_412570] using wordTrace_append hprefix tailTrace_412570
  have hstable : (prefixWord ++ tailWord_412570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412570).length < 2 ^ (prefixWord ++ tailWord_412570).sum := by decide
  have hdescent : baseEnd_412570 < baseStart_412570 := by decide
  rcases family_descends (prefixWord ++ tailWord_412570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412580 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 2]
def baseStart_412580 : Nat := 118140960795 + 412580 * 2 ^ 59
def prefixEnd_412580 : Nat := 4983230072969 + 3 ^ 40 * 412580 * 2
def baseEnd_412580 : Nat := 188312754161867566713409

theorem tailTrace_412580 : CollatzResearch.WordTrace tailWord_412580 prefixEnd_412580 188312754161867566713409 := by
  unfold tailWord_412580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524014422650298949629597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10032019230200398599506129 7524014422650298949629597)
  ·
    refine ⟨2821505408493862106111099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7524014422650298949629597 2821505408493862106111099)
    ·
      refine ⟨4232258112740793159166649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821505408493862106111099 4232258112740793159166649)
      ·
        refine ⟨3174193584555594869374987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4232258112740793159166649 3174193584555594869374987)
        ·
          refine ⟨4761290376833392304062481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174193584555594869374987 4761290376833392304062481)
          ·
            refine ⟨3570967782625044228046861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4761290376833392304062481 3570967782625044228046861)
            ·
              refine ⟨1339112918484391585517573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3570967782625044228046861 1339112918484391585517573)
              ·
                refine ⟨251083672215823422284545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1339112918484391585517573 251083672215823422284545)
                ·
                  refine ⟨188312754161867566713409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251083672215823422284545 188312754161867566713409)
                  ·
                    rfl

theorem cell20_412580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_412580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412580 prefixEnd_412580 := by exact prefixLift 412580
  have htrace : WordTrace (prefixWord ++ tailWord_412580) baseStart_412580 baseEnd_412580 := by
    simpa [prefixWord, tailWord_412580, baseEnd_412580] using wordTrace_append hprefix tailTrace_412580
  have hstable : (prefixWord ++ tailWord_412580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412580).length < 2 ^ (prefixWord ++ tailWord_412580).sum := by decide
  have hdescent : baseEnd_412580 < baseStart_412580 := by decide
  rcases family_descends (prefixWord ++ tailWord_412580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412591 : List Nat := [1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_412591 : Nat := 118140960795 + 412591 * 2 ^ 59
def prefixEnd_412591 : Nat := 4983230072969 + 3 ^ 40 * 412591 * 2
def baseEnd_412591 : Nat := 62772591620533472448899

theorem tailTrace_412591 : CollatzResearch.WordTrace tailWord_412591 prefixEnd_412591 62772591620533472448899 := by
  unfold tailWord_412591
  simp only [CollatzResearch.WordTrace]
  refine ⟨15048430048260746777909627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10032286698840497851939751 15048430048260746777909627)
  ·
    refine ⟨22572645072391120166864441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15048430048260746777909627 22572645072391120166864441)
    ·
      refine ⟨16929483804293340125148331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22572645072391120166864441 16929483804293340125148331)
      ·
        refine ⟨25394225706440010187722497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16929483804293340125148331 25394225706440010187722497)
        ·
          refine ⟨19045669279830007640791873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25394225706440010187722497 19045669279830007640791873)
          ·
            refine ⟨14284251959872505730593905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19045669279830007640791873 14284251959872505730593905)
            ·
              refine ⟨10713188969904379297945429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14284251959872505730593905 10713188969904379297945429)
              ·
                refine ⟨62772591620533472448899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10713188969904379297945429 62772591620533472448899)
                ·
                  rfl

theorem cell20_412591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_412591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412591 prefixEnd_412591 := by exact prefixLift 412591
  have htrace : WordTrace (prefixWord ++ tailWord_412591) baseStart_412591 baseEnd_412591 := by
    simpa [prefixWord, tailWord_412591, baseEnd_412591] using wordTrace_append hprefix tailTrace_412591
  have hstable : (prefixWord ++ tailWord_412591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412591).length < 2 ^ (prefixWord ++ tailWord_412591).sum := by decide
  have hdescent : baseEnd_412591 < baseStart_412591 := by decide
  rcases family_descends (prefixWord ++ tailWord_412591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412601 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_412601 : Nat := 118140960795 + 412601 * 2 ^ 59
def prefixEnd_412601 : Nat := 4983230072969 + 3 ^ 40 * 412601 * 2
def baseEnd_412601 : Nat := 188322339134084827013323

theorem tailTrace_412601 : CollatzResearch.WordTrace tailWord_412601 prefixEnd_412601 188322339134084827013323 := by
  unfold tailWord_412601
  simp only [CollatzResearch.WordTrace]
  refine ⟨15048794778224518485773657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10032529852149678990515771 15048794778224518485773657)
  ·
    refine ⟨11286596083668388864330243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15048794778224518485773657 11286596083668388864330243)
    ·
      refine ⟨16929894125502583296495365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11286596083668388864330243 16929894125502583296495365)
      ·
        refine ⟨3174355148531734368092881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16929894125502583296495365 3174355148531734368092881)
        ·
          refine ⟨2380766361398800776069661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3174355148531734368092881 2380766361398800776069661)
          ·
            refine ⟨892787385524550291026123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2380766361398800776069661 892787385524550291026123)
            ·
              refine ⟨1339181078286825436539185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892787385524550291026123 1339181078286825436539185)
              ·
                refine ⟨1004385808715119077404389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339181078286825436539185 1004385808715119077404389)
                ·
                  refine ⟨188322339134084827013323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004385808715119077404389 188322339134084827013323)
                  ·
                    rfl

theorem cell20_412601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_412601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412601 prefixEnd_412601 := by exact prefixLift 412601
  have htrace : WordTrace (prefixWord ++ tailWord_412601) baseStart_412601 baseEnd_412601 := by
    simpa [prefixWord, tailWord_412601, baseEnd_412601] using wordTrace_append hprefix tailTrace_412601
  have hstable : (prefixWord ++ tailWord_412601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412601).length < 2 ^ (prefixWord ++ tailWord_412601).sum := by decide
  have hdescent : baseEnd_412601 < baseStart_412601 := by decide
  rcases family_descends (prefixWord ++ tailWord_412601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412621 : List Nat := [1, 6, 3, 1, 1, 1, 7]
def baseStart_412621 : Nat := 118140960795 + 412621 * 2 ^ 59
def prefixEnd_412621 : Nat := 4983230072969 + 3 ^ 40 * 412621 * 2
def baseEnd_412621 : Nat := 20925718631005960705175

theorem tailTrace_412621 : CollatzResearch.WordTrace tailWord_412621 prefixEnd_412621 20925718631005960705175 := by
  unfold tailWord_412621
  simp only [CollatzResearch.WordTrace]
  refine ⟨15049524238152061901501717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10033016158768041267667811 15049524238152061901501717)
  ·
    refine ⟨705446448663377901632893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15049524238152061901501717 705446448663377901632893)
    ·
      refine ⟨264542418248766713112335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 705446448663377901632893 264542418248766713112335)
      ·
        refine ⟨396813627373150069668503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264542418248766713112335 396813627373150069668503)
        ·
          refine ⟨595220441059725104502755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396813627373150069668503 595220441059725104502755)
          ·
            refine ⟨892830661589587656754133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595220441059725104502755 892830661589587656754133)
            ·
              refine ⟨20925718631005960705175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 892830661589587656754133 20925718631005960705175)
              ·
                rfl

theorem cell20_412621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 7].length) (baseStart_412621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412621 prefixEnd_412621 := by exact prefixLift 412621
  have htrace : WordTrace (prefixWord ++ tailWord_412621) baseStart_412621 baseEnd_412621 := by
    simpa [prefixWord, tailWord_412621, baseEnd_412621] using wordTrace_append hprefix tailTrace_412621
  have hstable : (prefixWord ++ tailWord_412621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412621).length < 2 ^ (prefixWord ++ tailWord_412621).sum := by decide
  have hdescent : baseEnd_412621 < baseStart_412621 := by decide
  rcases family_descends (prefixWord ++ tailWord_412621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412632 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_412632 : Nat := 118140960795 + 412632 * 2 ^ 59
def prefixEnd_412632 : Nat := 4983230072969 + 3 ^ 40 * 412632 * 2
def baseEnd_412632 : Nat := 188336488378786496979863

theorem tailTrace_412632 : CollatzResearch.WordTrace tailWord_412632 prefixEnd_412632 188336488378786496979863 := by
  unfold tailWord_412632
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524962720556105390076075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10033283627408140520101433 7524962720556105390076075)
  ·
    refine ⟨11287444080834158085114113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7524962720556105390076075 11287444080834158085114113)
    ·
      refine ⟨8465583060625618563835585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11287444080834158085114113 8465583060625618563835585)
      ·
        refine ⟨6349187295469213922876689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8465583060625618563835585 6349187295469213922876689)
        ·
          refine ⟨4761890471601910442157517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6349187295469213922876689 4761890471601910442157517)
          ·
            refine ⟨1785708926850716415809069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4761890471601910442157517 1785708926850716415809069)
            ·
              refine ⟨669640847569018655928401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1785708926850716415809069 669640847569018655928401)
              ·
                refine ⟨502230635676763991946301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669640847569018655928401 502230635676763991946301)
                ·
                  refine ⟨188336488378786496979863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502230635676763991946301 188336488378786496979863)
                  ·
                    rfl

theorem cell20_412632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_412632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412632 prefixEnd_412632 := by exact prefixLift 412632
  have htrace : WordTrace (prefixWord ++ tailWord_412632) baseStart_412632 baseEnd_412632 := by
    simpa [prefixWord, tailWord_412632, baseEnd_412632] using wordTrace_append hprefix tailTrace_412632
  have hstable : (prefixWord ++ tailWord_412632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412632).length < 2 ^ (prefixWord ++ tailWord_412632).sum := by decide
  have hdescent : baseEnd_412632 < baseStart_412632 := by decide
  rcases family_descends (prefixWord ++ tailWord_412632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412673 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 2]
def baseStart_412673 : Nat := 118140960795 + 412673 * 2 ^ 59
def prefixEnd_412673 : Nat := 4983230072969 + 3 ^ 40 * 412673 * 2
def baseEnd_412673 : Nat := 188355201895972576613029

theorem tailTrace_412673 : CollatzResearch.WordTrace tailWord_412673 prefixEnd_412673 188355201895972576613029 := by
  unfold tailWord_412673
  simp only [CollatzResearch.WordTrace]
  refine ⟨15051420833963674782394673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10034280555975783188263115 15051420833963674782394673)
  ·
    refine ⟨11288565625472756086796005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15051420833963674782394673 11288565625472756086796005)
    ·
      refine ⟨2116606054776141766274251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11288565625472756086796005 2116606054776141766274251)
      ·
        refine ⟨3174909082164212649411377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116606054776141766274251 3174909082164212649411377)
        ·
          refine ⟨2381181811623159487058533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3174909082164212649411377 2381181811623159487058533)
          ·
            refine ⟨446471589679342403823475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2381181811623159487058533 446471589679342403823475)
            ·
              refine ⟨669707384519013605735213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446471589679342403823475 669707384519013605735213)
              ·
                refine ⟨251140269194630102150705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669707384519013605735213 251140269194630102150705)
                ·
                  refine ⟨188355201895972576613029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251140269194630102150705 188355201895972576613029)
                  ·
                    rfl

theorem cell20_412673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_412673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412673 prefixEnd_412673 := by exact prefixLift 412673
  have htrace : WordTrace (prefixWord ++ tailWord_412673) baseStart_412673 baseEnd_412673 := by
    simpa [prefixWord, tailWord_412673, baseEnd_412673] using wordTrace_append hprefix tailTrace_412673
  have hstable : (prefixWord ++ tailWord_412673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412673).length < 2 ^ (prefixWord ++ tailWord_412673).sum := by decide
  have hdescent : baseEnd_412673 < baseStart_412673 := by decide
  rcases family_descends (prefixWord ++ tailWord_412673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412684 : List Nat := [2, 2, 1, 2, 3, 4, 6]
def baseStart_412684 : Nat := 118140960795 + 412684 * 2 ^ 59
def prefixEnd_412684 : Nat := 4983230072969 + 3 ^ 40 * 412684 * 2
def baseEnd_412684 : Nat := 20928913621745047471813

theorem tailTrace_412684 : CollatzResearch.WordTrace tailWord_412684 prefixEnd_412684 20928913621745047471813 := by
  unfold tailWord_412684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7525911018461911830522553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10034548024615882440696737 7525911018461911830522553)
  ·
    refine ⟨5644433263846433872891915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7525911018461911830522553 5644433263846433872891915)
    ·
      refine ⟨8466649895769650809337873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5644433263846433872891915 8466649895769650809337873)
      ·
        refine ⟨6349987421827238107003405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8466649895769650809337873 6349987421827238107003405)
        ·
          refine ⟨2381245283185214290126277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6349987421827238107003405 2381245283185214290126277)
          ·
            refine ⟨446483490597227679398677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2381245283185214290126277 446483490597227679398677)
            ·
              refine ⟨20928913621745047471813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 446483490597227679398677 20928913621745047471813)
              ·
                rfl

theorem cell20_412684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 6].length) (baseStart_412684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412684 prefixEnd_412684 := by exact prefixLift 412684
  have htrace : WordTrace (prefixWord ++ tailWord_412684) baseStart_412684 baseEnd_412684 := by
    simpa [prefixWord, tailWord_412684, baseEnd_412684] using wordTrace_append hprefix tailTrace_412684
  have hstable : (prefixWord ++ tailWord_412684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412684).length < 2 ^ (prefixWord ++ tailWord_412684).sum := by decide
  have hdescent : baseEnd_412684 < baseStart_412684 := by decide
  rcases family_descends (prefixWord ++ tailWord_412684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412691 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_412691 : Nat := 118140960795 + 412691 * 2 ^ 59
def prefixEnd_412691 : Nat := 4983230072969 + 3 ^ 40 * 412691 * 2
def baseEnd_412691 : Nat := 188363417586444514012955

theorem tailTrace_412691 : CollatzResearch.WordTrace tailWord_412691 prefixEnd_412691 188363417586444514012955 := by
  unfold tailWord_412691
  simp only [CollatzResearch.WordTrace]
  refine ⟨15052077347898463856549927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10034718231932309237699951 15052077347898463856549927)
  ·
    refine ⟨22578116021847695784824891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15052077347898463856549927 22578116021847695784824891)
    ·
      refine ⟨33867174032771543677237337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22578116021847695784824891 33867174032771543677237337)
      ·
        refine ⟨25400380524578657757928003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33867174032771543677237337 25400380524578657757928003)
        ·
          refine ⟨38100570786867986636892005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25400380524578657757928003 38100570786867986636892005)
          ·
            refine ⟨7143857022537747494417251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38100570786867986636892005 7143857022537747494417251)
            ·
              refine ⟨10715785533806621241625877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143857022537747494417251 10715785533806621241625877)
              ·
                refine ⟨502302446897185370701213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10715785533806621241625877 502302446897185370701213)
                ·
                  refine ⟨188363417586444514012955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502302446897185370701213 188363417586444514012955)
                  ·
                    rfl

theorem cell20_412691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_412691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412691 prefixEnd_412691 := by exact prefixLift 412691
  have htrace : WordTrace (prefixWord ++ tailWord_412691) baseStart_412691 baseEnd_412691 := by
    simpa [prefixWord, tailWord_412691, baseEnd_412691] using wordTrace_append hprefix tailTrace_412691
  have hstable : (prefixWord ++ tailWord_412691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412691).length < 2 ^ (prefixWord ++ tailWord_412691).sum := by decide
  have hdescent : baseEnd_412691 < baseStart_412691 := by decide
  rcases family_descends (prefixWord ++ tailWord_412691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412701 : List Nat := [1, 4, 2, 2, 3, 1, 2, 5]
def baseStart_412701 : Nat := 118140960795 + 412701 * 2 ^ 59
def prefixEnd_412701 : Nat := 4983230072969 + 3 ^ 40 * 412701 * 2
def baseEnd_412701 : Nat := 62789327286309641226527

theorem tailTrace_412701 : CollatzResearch.WordTrace tailWord_412701 prefixEnd_412701 62789327286309641226527 := by
  unfold tailWord_412701
  simp only [CollatzResearch.WordTrace]
  refine ⟨15052442077862235564413957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10034961385241490376275971 15052442077862235564413957)
  ·
    refine ⟨2822332889599169168327617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15052442077862235564413957 2822332889599169168327617)
    ·
      refine ⟨2116749667199376876245713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2822332889599169168327617 2116749667199376876245713)
      ·
        refine ⟨1587562250399532657184285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2116749667199376876245713 1587562250399532657184285)
        ·
          refine ⟨595335843899824746444107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1587562250399532657184285 595335843899824746444107)
          ·
            refine ⟨893003765849737119666161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595335843899824746444107 893003765849737119666161)
            ·
              refine ⟨669752824387302839749621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893003765849737119666161 669752824387302839749621)
              ·
                refine ⟨62789327286309641226527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 669752824387302839749621 62789327286309641226527)
                ·
                  rfl

theorem cell20_412701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 5].length) (baseStart_412701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412701 prefixEnd_412701 := by exact prefixLift 412701
  have htrace : WordTrace (prefixWord ++ tailWord_412701) baseStart_412701 baseEnd_412701 := by
    simpa [prefixWord, tailWord_412701, baseEnd_412701] using wordTrace_append hprefix tailTrace_412701
  have hstable : (prefixWord ++ tailWord_412701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412701).length < 2 ^ (prefixWord ++ tailWord_412701).sum := by decide
  have hdescent : baseEnd_412701 < baseStart_412701 := by decide
  rcases family_descends (prefixWord ++ tailWord_412701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412742 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_412742 : Nat := 118140960795 + 412742 * 2 ^ 59
def prefixEnd_412742 : Nat := 4983230072969 + 3 ^ 40 * 412742 * 2
def baseEnd_412742 : Nat := 188386695376115003312747

theorem tailTrace_412742 : CollatzResearch.WordTrace tailWord_412742 prefixEnd_412742 188386695376115003312747 := by
  unfold tailWord_412742
  simp only [CollatzResearch.WordTrace]
  refine ⟨470435545959803111458015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10035958313809133044437653 470435545959803111458015)
  ·
    refine ⟨705653318939704667187023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470435545959803111458015 705653318939704667187023)
    ·
      refine ⟨1058479978409557000780535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705653318939704667187023 1058479978409557000780535)
      ·
        refine ⟨1587719967614335501170803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058479978409557000780535 1587719967614335501170803)
        ·
          refine ⟨2381579951421503251756205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587719967614335501170803 2381579951421503251756205)
          ·
            refine ⟨893092481783063719408577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2381579951421503251756205 893092481783063719408577)
            ·
              refine ⟨669819361337297789556433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893092481783063719408577 669819361337297789556433)
              ·
                refine ⟨502364521002973342167325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669819361337297789556433 502364521002973342167325)
                ·
                  refine ⟨188386695376115003312747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502364521002973342167325 188386695376115003312747)
                  ·
                    rfl

theorem cell20_412742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_412742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412742 prefixEnd_412742 := by exact prefixLift 412742
  have htrace : WordTrace (prefixWord ++ tailWord_412742) baseStart_412742 baseEnd_412742 := by
    simpa [prefixWord, tailWord_412742, baseEnd_412742] using wordTrace_append hprefix tailTrace_412742
  have hstable : (prefixWord ++ tailWord_412742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412742).length < 2 ^ (prefixWord ++ tailWord_412742).sum := by decide
  have hdescent : baseEnd_412742 < baseStart_412742 := by decide
  rcases family_descends (prefixWord ++ tailWord_412742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412743 : List Nat := [1, 1, 4, 1, 3, 10]
def baseStart_412743 : Nat := 118140960795 + 412743 * 2 ^ 59
def prefixEnd_412743 : Nat := 4983230072969 + 3 ^ 40 * 412743 * 2
def baseEnd_412743 : Nat := 6977301918643090528867

theorem tailTrace_412743 : CollatzResearch.WordTrace tailWord_412743 prefixEnd_412743 6977301918643090528867 := by
  unfold tailWord_412743
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053973943710076737442883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10035982629140051158295255 15053973943710076737442883)
  ·
    refine ⟨22580960915565115106164325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15053973943710076737442883 22580960915565115106164325)
    ·
      refine ⟨4233930171668459082405811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22580960915565115106164325 4233930171668459082405811)
      ·
        refine ⟨6350895257502688623608717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233930171668459082405811 6350895257502688623608717)
        ·
          refine ⟨2381585721563508233853269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6350895257502688623608717 2381585721563508233853269)
          ·
            refine ⟨6977301918643090528867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2381585721563508233853269 6977301918643090528867)
            ·
              rfl

theorem cell20_412743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 10].length) (baseStart_412743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412743 prefixEnd_412743 := by exact prefixLift 412743
  have htrace : WordTrace (prefixWord ++ tailWord_412743) baseStart_412743 baseEnd_412743 := by
    simpa [prefixWord, tailWord_412743, baseEnd_412743] using wordTrace_append hprefix tailTrace_412743
  have hstable : (prefixWord ++ tailWord_412743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412743).length < 2 ^ (prefixWord ++ tailWord_412743).sum := by decide
  have hdescent : baseEnd_412743 < baseStart_412743 := by decide
  rcases family_descends (prefixWord ++ tailWord_412743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412749 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 2]
def baseStart_412749 : Nat := 118140960795 + 412749 * 2 ^ 59
def prefixEnd_412749 : Nat := 4983230072969 + 3 ^ 40 * 412749 * 2
def baseEnd_412749 : Nat := 188389890366854090079385

theorem tailTrace_412749 : CollatzResearch.WordTrace tailWord_412749 prefixEnd_412749 188389890366854090079385 := by
  unfold tailWord_412749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054192781688339762161301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10036128521125559841440867 15054192781688339762161301)
  ·
    refine ⟨705665286641640926351311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15054192781688339762161301 705665286641640926351311)
    ·
      refine ⟨1058497929962461389526967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705665286641640926351311 1058497929962461389526967)
      ·
        refine ⟨1587746894943692084290451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058497929962461389526967 1587746894943692084290451)
        ·
          refine ⟨2381620342415538126435677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587746894943692084290451 2381620342415538126435677)
          ·
            refine ⟨893107628405826797413379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2381620342415538126435677 893107628405826797413379)
            ·
              refine ⟨1339661442608740196120069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893107628405826797413379 1339661442608740196120069)
              ·
                refine ⟨251186520489138786772513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1339661442608740196120069 251186520489138786772513)
                ·
                  refine ⟨188389890366854090079385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251186520489138786772513 188389890366854090079385)
                  ·
                    rfl

theorem cell20_412749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_412749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412749 prefixEnd_412749 := by exact prefixLift 412749
  have htrace : WordTrace (prefixWord ++ tailWord_412749) baseStart_412749 baseEnd_412749 := by
    simpa [prefixWord, tailWord_412749, baseEnd_412749] using wordTrace_append hprefix tailTrace_412749
  have hstable : (prefixWord ++ tailWord_412749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412749).length < 2 ^ (prefixWord ++ tailWord_412749).sum := by decide
  have hdescent : baseEnd_412749 < baseStart_412749 := by decide
  rcases family_descends (prefixWord ++ tailWord_412749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412767 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 3]
def baseStart_412767 : Nat := 118140960795 + 412767 * 2 ^ 59
def prefixEnd_412767 : Nat := 4983230072969 + 3 ^ 40 * 412767 * 2
def baseEnd_412767 : Nat := 188398106057326027479311

theorem tailTrace_412767 : CollatzResearch.WordTrace tailWord_412767 prefixEnd_412767 188398106057326027479311 := by
  unfold tailWord_412767
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054849295623128836316555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10036566197082085890877703 15054849295623128836316555)
  ·
    refine ⟨22582273943434693254474833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15054849295623128836316555 22582273943434693254474833)
    ·
      refine ⟨16936705457576019940856125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22582273943434693254474833 16936705457576019940856125)
      ·
        refine ⟨6351264546591007477821047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16936705457576019940856125 6351264546591007477821047)
        ·
          refine ⟨9526896819886511216731571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351264546591007477821047 9526896819886511216731571)
          ·
            refine ⟨14290345229829766825097357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526896819886511216731571 14290345229829766825097357)
            ·
              refine ⟨5358879461186162559411509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14290345229829766825097357 5358879461186162559411509)
              ·
                refine ⟨502394949486202739944829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5358879461186162559411509 502394949486202739944829)
                ·
                  refine ⟨188398106057326027479311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502394949486202739944829 188398106057326027479311)
                  ·
                    rfl

theorem cell20_412767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_412767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412767 prefixEnd_412767 := by exact prefixLift 412767
  have htrace : WordTrace (prefixWord ++ tailWord_412767) baseStart_412767 baseEnd_412767 := by
    simpa [prefixWord, tailWord_412767, baseEnd_412767] using wordTrace_append hprefix tailTrace_412767
  have hstable : (prefixWord ++ tailWord_412767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412767).length < 2 ^ (prefixWord ++ tailWord_412767).sum := by decide
  have hdescent : baseEnd_412767 < baseStart_412767 := by decide
  rcases family_descends (prefixWord ++ tailWord_412767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412770 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_412770 : Nat := 118140960795 + 412770 * 2 ^ 59
def prefixEnd_412770 : Nat := 4983230072969 + 3 ^ 40 * 412770 * 2
def baseEnd_412770 : Nat := 188399475339071350379299

theorem tailTrace_412770 : CollatzResearch.WordTrace tailWord_412770 prefixEnd_412770 188399475339071350379299 := by
  unfold tailWord_412770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763739678653065087168941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10036639143074840232450509 3763739678653065087168941)
  ·
    refine ⟨1411402379494899407688353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3763739678653065087168941 1411402379494899407688353)
    ·
      refine ⟨1058551784621174555766265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1411402379494899407688353 1058551784621174555766265)
      ·
        refine ⟨793913838465880916824699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058551784621174555766265 793913838465880916824699)
        ·
          refine ⟨1190870757698821375237049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793913838465880916824699 1190870757698821375237049)
          ·
            refine ⟨893153068274116031427787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190870757698821375237049 893153068274116031427787)
            ·
              refine ⟨1339729602411174047141681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893153068274116031427787 1339729602411174047141681)
              ·
                refine ⟨1004797201808380535356261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339729602411174047141681 1004797201808380535356261)
                ·
                  refine ⟨188399475339071350379299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004797201808380535356261 188399475339071350379299)
                  ·
                    rfl

theorem cell20_412770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_412770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412770 prefixEnd_412770 := by exact prefixLift 412770
  have htrace : WordTrace (prefixWord ++ tailWord_412770) baseStart_412770 baseEnd_412770 := by
    simpa [prefixWord, tailWord_412770, baseEnd_412770] using wordTrace_append hprefix tailTrace_412770
  have hstable : (prefixWord ++ tailWord_412770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412770).length < 2 ^ (prefixWord ++ tailWord_412770).sum := by decide
  have hdescent : baseEnd_412770 < baseStart_412770 := by decide
  rcases family_descends (prefixWord ++ tailWord_412770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412801 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 3]
def baseStart_412801 : Nat := 118140960795 + 412801 * 2 ^ 59
def prefixEnd_412801 : Nat := 4983230072969 + 3 ^ 40 * 412801 * 2
def baseEnd_412801 : Nat := 188413624583773020345839

theorem tailTrace_412801 : CollatzResearch.WordTrace tailWord_412801 prefixEnd_412801 188413624583773020345839 := by
  unfold tailWord_412801
  simp only [CollatzResearch.WordTrace]
  refine ⟨15056089377499952643054257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10037392918333301762036171 15056089377499952643054257)
  ·
    refine ⟨11292067033124964482290693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15056089377499952643054257 11292067033124964482290693)
    ·
      refine ⟨2117262568710930840429505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11292067033124964482290693 2117262568710930840429505)
      ·
        refine ⟨1587946926533198130322129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2117262568710930840429505 1587946926533198130322129)
        ·
          refine ⟨1190960194899898597741597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587946926533198130322129 1190960194899898597741597)
          ·
            refine ⟨446610073087461974153099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1190960194899898597741597 446610073087461974153099)
            ·
              refine ⟨669915109631192961229649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446610073087461974153099 669915109631192961229649)
              ·
                refine ⟨502436332223394720922237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669915109631192961229649 502436332223394720922237)
                ·
                  refine ⟨188413624583773020345839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502436332223394720922237 188413624583773020345839)
                  ·
                    rfl

theorem cell20_412801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_412801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412801 prefixEnd_412801 := by exact prefixLift 412801
  have htrace : WordTrace (prefixWord ++ tailWord_412801) baseStart_412801 baseEnd_412801 := by
    simpa [prefixWord, tailWord_412801, baseEnd_412801] using wordTrace_append hprefix tailTrace_412801
  have hstable : (prefixWord ++ tailWord_412801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412801).length < 2 ^ (prefixWord ++ tailWord_412801).sum := by decide
  have hdescent : baseEnd_412801 < baseStart_412801 := by decide
  rcases family_descends (prefixWord ++ tailWord_412801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412808 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_412808 : Nat := 118140960795 + 412808 * 2 ^ 59
def prefixEnd_412808 : Nat := 4983230072969 + 3 ^ 40 * 412808 * 2
def baseEnd_412808 : Nat := 188416819574512107112477

theorem tailTrace_412808 : CollatzResearch.WordTrace tailWord_412808 prefixEnd_412808 188416819574512107112477 := by
  unfold tailWord_412808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528172344237296419279539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10037563125649728559039385 7528172344237296419279539)
  ·
    refine ⟨11292258516355944628919309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7528172344237296419279539 11292258516355944628919309)
    ·
      refine ⟨4234596943633479235844741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11292258516355944628919309 4234596943633479235844741)
      ·
        refine ⟨793986926931277356720889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4234596943633479235844741 793986926931277356720889)
        ·
          refine ⟨595490195198458017540667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793986926931277356720889 595490195198458017540667)
          ·
            refine ⟨893235292797687026311001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595490195198458017540667 893235292797687026311001)
            ·
              refine ⟨669926469598265269733251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893235292797687026311001 669926469598265269733251)
              ·
                refine ⟨1004889704397397904599877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669926469598265269733251 1004889704397397904599877)
                ·
                  refine ⟨188416819574512107112477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004889704397397904599877 188416819574512107112477)
                  ·
                    rfl

theorem cell20_412808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_412808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412808 prefixEnd_412808 := by exact prefixLift 412808
  have htrace : WordTrace (prefixWord ++ tailWord_412808) baseStart_412808 baseEnd_412808 := by
    simpa [prefixWord, tailWord_412808, baseEnd_412808] using wordTrace_append hprefix tailTrace_412808
  have hstable : (prefixWord ++ tailWord_412808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412808).length < 2 ^ (prefixWord ++ tailWord_412808).sum := by decide
  have hdescent : baseEnd_412808 < baseStart_412808 := by decide
  rcases family_descends (prefixWord ++ tailWord_412808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412836 : List Nat := [2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_412836 : Nat := 118140960795 + 412836 * 2 ^ 59
def prefixEnd_412836 : Nat := 4983230072969 + 3 ^ 40 * 412836 * 2
def baseEnd_412836 : Nat := 62809866512489484726343

theorem tailTrace_412836 : CollatzResearch.WordTrace tailWord_412836 prefixEnd_412836 62809866512489484726343 := by
  unfold tailWord_412836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528682966186576810289181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10038243954915435747052241 7528682966186576810289181)
  ·
    refine ⟨2823256112319966303858443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7528682966186576810289181 2823256112319966303858443)
    ·
      refine ⟨4234884168479949455787665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823256112319966303858443 4234884168479949455787665)
      ·
        refine ⟨3176163126359962091840749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4234884168479949455787665 3176163126359962091840749)
        ·
          refine ⟨1191061172384985784440281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3176163126359962091840749 1191061172384985784440281)
          ·
            refine ⟨893295879288739338330211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191061172384985784440281 893295879288739338330211)
            ·
              refine ⟨1339943818933109007495317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893295879288739338330211 1339943818933109007495317)
              ·
                refine ⟨62809866512489484726343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1339943818933109007495317 62809866512489484726343)
                ·
                  rfl

theorem cell20_412836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_412836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412836 prefixEnd_412836 := by exact prefixLift 412836
  have htrace : WordTrace (prefixWord ++ tailWord_412836) baseStart_412836 baseEnd_412836 := by
    simpa [prefixWord, tailWord_412836, baseEnd_412836] using wordTrace_append hprefix tailTrace_412836
  have hstable : (prefixWord ++ tailWord_412836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412836).length < 2 ^ (prefixWord ++ tailWord_412836).sum := by decide
  have hdescent : baseEnd_412836 < baseStart_412836 := by decide
  rcases family_descends (prefixWord ++ tailWord_412836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412842 : List Nat := [3, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_412842 : Nat := 118140960795 + 412842 * 2 ^ 59
def prefixEnd_412842 : Nat := 4983230072969 + 3 ^ 40 * 412842 * 2
def baseEnd_412842 : Nat := 188432338100959099979005

theorem tailTrace_412842 : CollatzResearch.WordTrace tailWord_412842 prefixEnd_412842 188432338100959099979005 := by
  unfold tailWord_412842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764396192587854161324195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10038389846900944430197853 3764396192587854161324195)
  ·
    refine ⟨5646594288881781241986293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3764396192587854161324195 5646594288881781241986293)
    ·
      refine ⟨529368214582666991436215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5646594288881781241986293 529368214582666991436215)
      ·
        refine ⟨794052321874000487154323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529368214582666991436215 794052321874000487154323)
        ·
          refine ⟨1191078482811000730731485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794052321874000487154323 1191078482811000730731485)
          ·
            refine ⟨446654431054125274024307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1191078482811000730731485 446654431054125274024307)
            ·
              refine ⟨669981646581187911036461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446654431054125274024307 669981646581187911036461)
              ·
                refine ⟨251243117467945466638673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669981646581187911036461 251243117467945466638673)
                ·
                  refine ⟨188432338100959099979005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251243117467945466638673 188432338100959099979005)
                  ·
                    rfl

theorem cell20_412842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_412842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412842 prefixEnd_412842 := by exact prefixLift 412842
  have htrace : WordTrace (prefixWord ++ tailWord_412842) baseStart_412842 baseEnd_412842 := by
    simpa [prefixWord, tailWord_412842, baseEnd_412842] using wordTrace_append hprefix tailTrace_412842
  have hstable : (prefixWord ++ tailWord_412842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412842).length < 2 ^ (prefixWord ++ tailWord_412842).sum := by decide
  have hdescent : baseEnd_412842 < baseStart_412842 := by decide
  rcases family_descends (prefixWord ++ tailWord_412842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412857 : List Nat := [1, 2, 1, 4, 1, 3, 8]
def baseStart_412857 : Nat := 118140960795 + 412857 * 2 ^ 59
def prefixEnd_412857 : Nat := 4983230072969 + 3 ^ 40 * 412857 * 2
def baseEnd_412857 : Nat := 20937687167742857164327

theorem tailTrace_412857 : CollatzResearch.WordTrace tailWord_412857 prefixEnd_412857 20937687167742857164327 := by
  unfold tailWord_412857
  simp only [CollatzResearch.WordTrace]
  refine ⟨15058131865297074207092825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10038754576864716138061883 15058131865297074207092825)
  ·
    refine ⟨11293598898972805655319619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15058131865297074207092825 11293598898972805655319619)
    ·
      refine ⟨16940398348459208482979429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11293598898972805655319619 16940398348459208482979429)
      ·
        refine ⟨3176324690336101590558643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16940398348459208482979429 3176324690336101590558643)
        ·
          refine ⟨4764487035504152385837965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176324690336101590558643 4764487035504152385837965)
          ·
            refine ⟨1786682638314057144689237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4764487035504152385837965 1786682638314057144689237)
            ·
              refine ⟨20937687167742857164327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1786682638314057144689237 20937687167742857164327)
              ·
                rfl

theorem cell20_412857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_412857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412857 prefixEnd_412857 := by exact prefixLift 412857
  have htrace : WordTrace (prefixWord ++ tailWord_412857) baseStart_412857 baseEnd_412857 := by
    simpa [prefixWord, tailWord_412857, baseEnd_412857] using wordTrace_append hprefix tailTrace_412857
  have hstable : (prefixWord ++ tailWord_412857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412857).length < 2 ^ (prefixWord ++ tailWord_412857).sum := by decide
  have hdescent : baseEnd_412857 < baseStart_412857 := by decide
  rcases family_descends (prefixWord ++ tailWord_412857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412874 : List Nat := [3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_412874 : Nat := 118140960795 + 412874 * 2 ^ 59
def prefixEnd_412874 : Nat := 4983230072969 + 3 ^ 40 * 412874 * 2
def baseEnd_412874 : Nat := 62815647924303070304069

theorem tailTrace_412874 : CollatzResearch.WordTrace tailWord_412874 prefixEnd_412874 62815647924303070304069 := by
  unfold tailWord_412874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764687976558871527615419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10039167937490324073641117 3764687976558871527615419)
  ·
    refine ⟨5647031964838307291423129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3764687976558871527615419 5647031964838307291423129)
    ·
      refine ⟨4235273973628730468567347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5647031964838307291423129 4235273973628730468567347)
      ·
        refine ⟨6352910960443095702851021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235273973628730468567347 6352910960443095702851021)
        ·
          refine ⟨2382341610166160888569133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6352910960443095702851021 2382341610166160888569133)
          ·
            refine ⟨893378103812310333213425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2382341610166160888569133 893378103812310333213425)
            ·
              refine ⟨670033577859232749910069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893378103812310333213425 670033577859232749910069)
              ·
                refine ⟨62815647924303070304069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670033577859232749910069 62815647924303070304069)
                ·
                  rfl

theorem cell20_412874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_412874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412874 prefixEnd_412874 := by exact prefixLift 412874
  have htrace : WordTrace (prefixWord ++ tailWord_412874) baseStart_412874 baseEnd_412874 := by
    simpa [prefixWord, tailWord_412874, baseEnd_412874] using wordTrace_append hprefix tailTrace_412874
  have hstable : (prefixWord ++ tailWord_412874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412874).length < 2 ^ (prefixWord ++ tailWord_412874).sum := by decide
  have hdescent : baseEnd_412874 < baseStart_412874 := by decide
  rcases family_descends (prefixWord ++ tailWord_412874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412895 : List Nat := [1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_412895 : Nat := 118140960795 + 412895 * 2 ^ 59
def prefixEnd_412895 : Nat := 4983230072969 + 3 ^ 40 * 412895 * 2
def baseEnd_412895 : Nat := 62818842915042157070707

theorem tailTrace_412895 : CollatzResearch.WordTrace tailWord_412895 prefixEnd_412895 62818842915042157070707 := by
  unfold tailWord_412895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15059517839159406696976139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10039678559439604464650759 15059517839159406696976139)
  ·
    refine ⟨22589276758739110045464209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15059517839159406696976139 22589276758739110045464209)
    ·
      refine ⟨16941957569054332534098157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22589276758739110045464209 16941957569054332534098157)
      ·
        refine ⟨6353234088395374700286809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16941957569054332534098157 6353234088395374700286809)
        ·
          refine ⟨4764925566296531025215107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6353234088395374700286809 4764925566296531025215107)
          ·
            refine ⟨7147388349444796537822661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764925566296531025215107 7147388349444796537822661)
            ·
              refine ⟨1340135315520899350841749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7147388349444796537822661 1340135315520899350841749)
              ·
                refine ⟨62818842915042157070707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1340135315520899350841749 62818842915042157070707)
                ·
                  rfl

theorem cell20_412895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_412895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412895 prefixEnd_412895 := by exact prefixLift 412895
  have htrace : WordTrace (prefixWord ++ tailWord_412895) baseStart_412895 baseEnd_412895 := by
    simpa [prefixWord, tailWord_412895, baseEnd_412895] using wordTrace_append hprefix tailTrace_412895
  have hstable : (prefixWord ++ tailWord_412895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412895).length < 2 ^ (prefixWord ++ tailWord_412895).sum := by decide
  have hdescent : baseEnd_412895 < baseStart_412895 := by decide
  rcases family_descends (prefixWord ++ tailWord_412895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412964 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_412964 : Nat := 118140960795 + 412964 * 2 ^ 59
def prefixEnd_412964 : Nat := 4983230072969 + 3 ^ 40 * 412964 * 2
def baseEnd_412964 : Nat := 188488022225268897911839

theorem tailTrace_412964 : CollatzResearch.WordTrace tailWord_412964 prefixEnd_412964 188488022225268897911839 := by
  unfold tailWord_412964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7531017237954715740618973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10041356317272954320825297 7531017237954715740618973)
  ·
    refine ⟨2824131464233018402732115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7531017237954715740618973 2824131464233018402732115)
    ·
      refine ⟨4236197196349527604098173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824131464233018402732115 4236197196349527604098173)
      ·
        refine ⟨1588573948631072851536815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4236197196349527604098173 1588573948631072851536815)
        ·
          refine ⟨2382860922946609277305223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588573948631072851536815 2382860922946609277305223)
          ·
            refine ⟨3574291384419913915957835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382860922946609277305223 3574291384419913915957835)
            ·
              refine ⟨5361437076629870873936753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574291384419913915957835 5361437076629870873936753)
              ·
                refine ⟨4021077807472403155452565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361437076629870873936753 4021077807472403155452565)
                ·
                  refine ⟨188488022225268897911839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4021077807472403155452565 188488022225268897911839)
                  ·
                    rfl

theorem cell20_412964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_412964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412964 prefixEnd_412964 := by exact prefixLift 412964
  have htrace : WordTrace (prefixWord ++ tailWord_412964) baseStart_412964 baseEnd_412964 := by
    simpa [prefixWord, tailWord_412964, baseEnd_412964] using wordTrace_append hprefix tailTrace_412964
  have hstable : (prefixWord ++ tailWord_412964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412964).length < 2 ^ (prefixWord ++ tailWord_412964).sum := by decide
  have hdescent : baseEnd_412964 < baseStart_412964 := by decide
  rcases family_descends (prefixWord ++ tailWord_412964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412981 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_412981 : Nat := 118140960795 + 412981 * 2 ^ 59
def prefixEnd_412981 : Nat := 4983230072969 + 3 ^ 40 * 412981 * 2
def baseEnd_412981 : Nat := 188495781488492394345103

theorem tailTrace_412981 : CollatzResearch.WordTrace tailWord_412981 prefixEnd_412981 188495781488492394345103 := by
  unfold tailWord_412981
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062654516847843384606797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10041769677898562256404531 15062654516847843384606797)
  ·
    refine ⟨5648495443817941269227549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15062654516847843384606797 5648495443817941269227549)
    ·
      refine ⟨2118185791431727975960331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5648495443817941269227549 2118185791431727975960331)
      ·
        refine ⟨3177278687147591963940497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118185791431727975960331 3177278687147591963940497)
        ·
          refine ⟨2382959015360693972955373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3177278687147591963940497 2382959015360693972955373)
          ·
            refine ⟨893609630760260239858265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2382959015360693972955373 893609630760260239858265)
            ·
              refine ⟨670207223070195179893699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893609630760260239858265 670207223070195179893699)
              ·
                refine ⟨1005310834605292769840549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670207223070195179893699 1005310834605292769840549)
                ·
                  refine ⟨188495781488492394345103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005310834605292769840549 188495781488492394345103)
                  ·
                    rfl

theorem cell20_412981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_412981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_412981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_412981 prefixEnd_412981 := by exact prefixLift 412981
  have htrace : WordTrace (prefixWord ++ tailWord_412981) baseStart_412981 baseEnd_412981 := by
    simpa [prefixWord, tailWord_412981, baseEnd_412981] using wordTrace_append hprefix tailTrace_412981
  have hstable : (prefixWord ++ tailWord_412981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412981).length < 2 ^ (prefixWord ++ tailWord_412981).sum := by decide
  have hdescent : baseEnd_412981 < baseStart_412981 := by decide
  rcases family_descends (prefixWord ++ tailWord_412981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413009 : List Nat := [1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_413009 : Nat := 118140960795 + 413009 * 2 ^ 59
def prefixEnd_413009 : Nat := 4983230072969 + 3 ^ 40 * 413009 * 2
def baseEnd_413009 : Nat := 62836187150482913803885

theorem tailTrace_413009 : CollatzResearch.WordTrace tailWord_413009 prefixEnd_413009 62836187150482913803885 := by
  unfold tailWord_413009
  simp only [CollatzResearch.WordTrace]
  refine ⟨15063675760746404166626081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10042450507164269444417387 15063675760746404166626081)
  ·
    refine ⟨11297756820559803124969561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15063675760746404166626081 11297756820559803124969561)
    ·
      refine ⟨8473317615419852343727171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11297756820559803124969561 8473317615419852343727171)
      ·
        refine ⟨12709976423129778515590757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8473317615419852343727171 12709976423129778515590757)
        ·
          refine ⟨2383120579336833471673267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12709976423129778515590757 2383120579336833471673267)
          ·
            refine ⟨3574680869005250207509901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383120579336833471673267 3574680869005250207509901)
            ·
              refine ⟨1340505325876968827816213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3574680869005250207509901 1340505325876968827816213)
              ·
                refine ⟨62836187150482913803885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1340505325876968827816213 62836187150482913803885)
                ·
                  rfl

theorem cell20_413009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_413009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413009 prefixEnd_413009 := by exact prefixLift 413009
  have htrace : WordTrace (prefixWord ++ tailWord_413009) baseStart_413009 baseEnd_413009 := by
    simpa [prefixWord, tailWord_413009, baseEnd_413009] using wordTrace_append hprefix tailTrace_413009
  have hstable : (prefixWord ++ tailWord_413009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413009).length < 2 ^ (prefixWord ++ tailWord_413009).sum := by decide
  have hdescent : baseEnd_413009 < baseStart_413009 := by decide
  rcases family_descends (prefixWord ++ tailWord_413009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413016 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_413016 : Nat := 118140960795 + 413016 * 2 ^ 59
def prefixEnd_413016 : Nat := 4983230072969 + 3 ^ 40 * 413016 * 2
def baseEnd_413016 : Nat := 188511756442187828178293

theorem tailTrace_413016 : CollatzResearch.WordTrace tailWord_413016 prefixEnd_413016 188511756442187828178293 := by
  unfold tailWord_413016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7531965535860522181065451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10042620714480696241420601 7531965535860522181065451)
  ·
    refine ⟨11297948303790783271598177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7531965535860522181065451 11297948303790783271598177)
    ·
      refine ⟨8473461227843087453698633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11297948303790783271598177 8473461227843087453698633)
      ·
        refine ⟨6355095920882315590273975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8473461227843087453698633 6355095920882315590273975)
        ·
          refine ⟨9532643881323473385410963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355095920882315590273975 9532643881323473385410963)
          ·
            refine ⟨14298965821985210078116445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9532643881323473385410963 14298965821985210078116445)
            ·
              refine ⟨5362112183244453779293667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14298965821985210078116445 5362112183244453779293667)
              ·
                refine ⟨8043168274866680668940501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362112183244453779293667 8043168274866680668940501)
                ·
                  refine ⟨188511756442187828178293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8043168274866680668940501 188511756442187828178293)
                  ·
                    rfl

theorem cell20_413016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_413016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413016 prefixEnd_413016 := by exact prefixLift 413016
  have htrace : WordTrace (prefixWord ++ tailWord_413016) baseStart_413016 baseEnd_413016 := by
    simpa [prefixWord, tailWord_413016, baseEnd_413016] using wordTrace_append hprefix tailTrace_413016
  have hstable : (prefixWord ++ tailWord_413016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413016).length < 2 ^ (prefixWord ++ tailWord_413016).sum := by decide
  have hdescent : baseEnd_413016 < baseStart_413016 := by decide
  rcases family_descends (prefixWord ++ tailWord_413016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413047 : List Nat := [1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_413047 : Nat := 118140960795 + 413047 * 2 ^ 59
def prefixEnd_413047 : Nat := 4983230072969 + 3 ^ 40 * 413047 * 2
def baseEnd_413047 : Nat := 62841968562296499381611

theorem tailTrace_413047 : CollatzResearch.WordTrace tailWord_413047 prefixEnd_413047 62841968562296499381611 := by
  unfold tailWord_413047
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065061734608736656509395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10043374489739157771006263 15065061734608736656509395)
  ·
    refine ⟨22597592601913104984764093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15065061734608736656509395 22597592601913104984764093)
    ·
      refine ⟨8474097225717414369286535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22597592601913104984764093 8474097225717414369286535)
      ·
        refine ⟨12711145838576121553929803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474097225717414369286535 12711145838576121553929803)
        ·
          refine ⟨19066718757864182330894705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711145838576121553929803 19066718757864182330894705)
          ·
            refine ⟨14300039068398136748171029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19066718757864182330894705 14300039068398136748171029)
            ·
              refine ⟨670314331331162660070517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14300039068398136748171029 670314331331162660070517)
              ·
                refine ⟨62841968562296499381611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670314331331162660070517 62841968562296499381611)
                ·
                  rfl

theorem cell20_413047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_413047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413047 prefixEnd_413047 := by exact prefixLift 413047
  have htrace : WordTrace (prefixWord ++ tailWord_413047) baseStart_413047 baseEnd_413047 := by
    simpa [prefixWord, tailWord_413047, baseEnd_413047] using wordTrace_append hprefix tailTrace_413047
  have hstable : (prefixWord ++ tailWord_413047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413047).length < 2 ^ (prefixWord ++ tailWord_413047).sum := by decide
  have hdescent : baseEnd_413047 < baseStart_413047 := by decide
  rcases family_descends (prefixWord ++ tailWord_413047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413085 : List Nat := [1, 4, 2, 1, 3, 9]
def baseStart_413085 : Nat := 118140960795 + 413085 * 2 ^ 59
def prefixEnd_413085 : Nat := 4983230072969 + 3 ^ 40 * 413085 * 2
def baseEnd_413085 : Nat := 6983083330456676106593

theorem tailTrace_413085 : CollatzResearch.WordTrace tailWord_413085 prefixEnd_413085 6983083330456676106593 := by
  unfold tailWord_413085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15066447708471069146392709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10044298472314046097595139 15066447708471069146392709)
  ·
    refine ⟨2824958945338325464948633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15066447708471069146392709 2824958945338325464948633)
    ·
      refine ⟨2118719209003744098711475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2824958945338325464948633 2118719209003744098711475)
      ·
        refine ⟨3178078813505616148067213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118719209003744098711475 3178078813505616148067213)
        ·
          refine ⟨1191779555064606055525205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3178078813505616148067213 1191779555064606055525205)
          ·
            refine ⟨6983083330456676106593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1191779555064606055525205 6983083330456676106593)
            ·
              rfl

theorem cell20_413085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 9].length) (baseStart_413085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413085 prefixEnd_413085 := by exact prefixLift 413085
  have htrace : WordTrace (prefixWord ++ tailWord_413085) baseStart_413085 baseEnd_413085 := by
    simpa [prefixWord, tailWord_413085, baseEnd_413085] using wordTrace_append hprefix tailTrace_413085
  have hstable : (prefixWord ++ tailWord_413085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413085).length < 2 ^ (prefixWord ++ tailWord_413085).sum := by decide
  have hdescent : baseEnd_413085 < baseStart_413085 := by decide
  rcases family_descends (prefixWord ++ tailWord_413085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413140 : List Nat := [2, 4, 1, 2, 3, 1, 7]
def baseStart_413140 : Nat := 118140960795 + 413140 * 2 ^ 59
def prefixEnd_413140 : Nat := 4983230072969 + 3 ^ 40 * 413140 * 2
def baseEnd_413140 : Nat := 20952039268999389782717

theorem tailTrace_413140 : CollatzResearch.WordTrace tailWord_413140 prefixEnd_413140 20952039268999389782717 := by
  unfold tailWord_413140
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534226861635906769822437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10045635815514542359763249 7534226861635906769822437)
  ·
    refine ⟨1412667536556732519341707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7534226861635906769822437 1412667536556732519341707)
    ·
      refine ⟨2119001304835098779012561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412667536556732519341707 2119001304835098779012561)
      ·
        refine ⟨1589250978626324084259421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2119001304835098779012561 1589250978626324084259421)
        ·
          refine ⟨595969116984871531597283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1589250978626324084259421 595969116984871531597283)
          ·
            refine ⟨893953675477307297395925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595969116984871531597283 893953675477307297395925)
            ·
              refine ⟨20952039268999389782717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 893953675477307297395925 20952039268999389782717)
              ·
                rfl

theorem cell20_413140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 7].length) (baseStart_413140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413140 prefixEnd_413140 := by exact prefixLift 413140
  have htrace : WordTrace (prefixWord ++ tailWord_413140) baseStart_413140 baseEnd_413140 := by
    simpa [prefixWord, tailWord_413140, baseEnd_413140] using wordTrace_append hprefix tailTrace_413140
  have hstable : (prefixWord ++ tailWord_413140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413140).length < 2 ^ (prefixWord ++ tailWord_413140).sum := by decide
  have hdescent : baseEnd_413140 < baseStart_413140 := by decide
  rcases family_descends (prefixWord ++ tailWord_413140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413175 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_413175 : Nat := 118140960795 + 413175 * 2 ^ 59
def prefixEnd_413175 : Nat := 4983230072969 + 3 ^ 40 * 413175 * 2
def baseEnd_413175 : Nat := 188584328374689941877643

theorem tailTrace_413175 : CollatzResearch.WordTrace tailWord_413175 prefixEnd_413175 188584328374689941877643 := by
  unfold tailWord_413175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15069730278145014517168979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10046486852096676344779319 15069730278145014517168979)
  ·
    refine ⟨22604595417217521775753469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15069730278145014517168979 22604595417217521775753469)
    ·
      refine ⟨8476723281456570665907551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22604595417217521775753469 8476723281456570665907551)
      ·
        refine ⟨12715084922184855998861327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476723281456570665907551 12715084922184855998861327)
        ·
          refine ⟨19072627383277283998291991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12715084922184855998861327 19072627383277283998291991)
          ·
            refine ⟨28608941074915925997437987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19072627383277283998291991 28608941074915925997437987)
            ·
              refine ⟨42913411612373888996156981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28608941074915925997437987 42913411612373888996156981)
              ·
                refine ⟨4023132338660052093389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42913411612373888996156981 4023132338660052093389717)
                ·
                  refine ⟨188584328374689941877643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4023132338660052093389717 188584328374689941877643)
                  ·
                    rfl

theorem cell20_413175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_413175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413175 prefixEnd_413175 := by exact prefixLift 413175
  have htrace : WordTrace (prefixWord ++ tailWord_413175) baseStart_413175 baseEnd_413175 := by
    simpa [prefixWord, tailWord_413175, baseEnd_413175] using wordTrace_append hprefix tailTrace_413175
  have hstable : (prefixWord ++ tailWord_413175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413175).length < 2 ^ (prefixWord ++ tailWord_413175).sum := by decide
  have hdescent : baseEnd_413175 < baseStart_413175 := by decide
  rcases family_descends (prefixWord ++ tailWord_413175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413216 : List Nat := [2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_413216 : Nat := 118140960795 + 413216 * 2 ^ 59
def prefixEnd_413216 : Nat := 4983230072969 + 3 ^ 40 * 413216 * 2
def baseEnd_413216 : Nat := 62867680630625340503603

theorem tailTrace_413216 : CollatzResearch.WordTrace tailWord_413216 prefixEnd_413216 62867680630625340503603 := by
  unfold tailWord_413216
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535612835498239259705751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10047483780664319012941001 7535612835498239259705751)
  ·
    refine ⟨11303419253247358889558627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7535612835498239259705751 11303419253247358889558627)
    ·
      refine ⟨16955128879871038334337941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11303419253247358889558627 16955128879871038334337941)
      ·
        refine ⟨794771666243954921922091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16955128879871038334337941 794771666243954921922091)
        ·
          refine ⟨1192157499365932382883137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794771666243954921922091 1192157499365932382883137)
          ·
            refine ⟨894118124524449287162353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192157499365932382883137 894118124524449287162353)
            ·
              refine ⟨670588593393336965371765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894118124524449287162353 670588593393336965371765)
              ·
                refine ⟨62867680630625340503603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670588593393336965371765 62867680630625340503603)
                ·
                  rfl

theorem cell20_413216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_413216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413216 prefixEnd_413216 := by exact prefixLift 413216
  have htrace : WordTrace (prefixWord ++ tailWord_413216) baseStart_413216 baseEnd_413216 := by
    simpa [prefixWord, tailWord_413216, baseEnd_413216] using wordTrace_append hprefix tailTrace_413216
  have hstable : (prefixWord ++ tailWord_413216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413216).length < 2 ^ (prefixWord ++ tailWord_413216).sum := by decide
  have hdescent : baseEnd_413216 < baseStart_413216 := by decide
  rcases family_descends (prefixWord ++ tailWord_413216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413219 : List Nat := [1, 1, 1, 4, 5, 2, 2, 1, 3]
def baseStart_413219 : Nat := 118140960795 + 413219 * 2 ^ 59
def prefixEnd_413219 : Nat := 4983230072969 + 3 ^ 40 * 413219 * 2
def baseEnd_413219 : Nat := 188604411173621344410797

theorem tailTrace_413219 : CollatzResearch.WordTrace tailWord_413219 prefixEnd_413219 188604411173621344410797 := by
  unfold tailWord_413219
  simp only [CollatzResearch.WordTrace]
  refine ⟨15071335089985610031770711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10047556726657073354513807 15071335089985610031770711)
  ·
    refine ⟨22607002634978415047656067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15071335089985610031770711 22607002634978415047656067)
    ·
      refine ⟨33910503952467622571484101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22607002634978415047656067 33910503952467622571484101)
      ·
        refine ⟨6358219491087679232153269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33910503952467622571484101 6358219491087679232153269)
        ·
          refine ⟨596083077289469928014369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6358219491087679232153269 596083077289469928014369)
          ·
            refine ⟨447062307967102446010777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596083077289469928014369 447062307967102446010777)
            ·
              refine ⟨335296730975326834508083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447062307967102446010777 335296730975326834508083)
              ·
                refine ⟨502945096462990251762125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335296730975326834508083 502945096462990251762125)
                ·
                  refine ⟨188604411173621344410797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502945096462990251762125 188604411173621344410797)
                  ·
                    rfl

theorem cell20_413219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_413219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413219 prefixEnd_413219 := by exact prefixLift 413219
  have htrace : WordTrace (prefixWord ++ tailWord_413219) baseStart_413219 baseEnd_413219 := by
    simpa [prefixWord, tailWord_413219, baseEnd_413219] using wordTrace_append hprefix tailTrace_413219
  have hstable : (prefixWord ++ tailWord_413219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413219).length < 2 ^ (prefixWord ++ tailWord_413219).sum := by decide
  have hdescent : baseEnd_413219 < baseStart_413219 := by decide
  rcases family_descends (prefixWord ++ tailWord_413219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413237 : List Nat := [1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_413237 : Nat := 118140960795 + 413237 * 2 ^ 59
def prefixEnd_413237 : Nat := 4983230072969 + 3 ^ 40 * 413237 * 2
def baseEnd_413237 : Nat := 62870875621364427270241

theorem tailTrace_413237 : CollatzResearch.WordTrace tailWord_413237 prefixEnd_413237 62870875621364427270241 := by
  unfold tailWord_413237
  simp only [CollatzResearch.WordTrace]
  refine ⟨15071991603920399105925965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10047994402613599403950643 15071991603920399105925965)
  ·
    refine ⟨5651996851470149664722237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15071991603920399105925965 5651996851470149664722237)
    ·
      refine ⟨2119498819301306124270839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5651996851470149664722237 2119498819301306124270839)
      ·
        refine ⟨3179248228951959186406259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119498819301306124270839 3179248228951959186406259)
        ·
          refine ⟨4768872343427938779609389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179248228951959186406259 4768872343427938779609389)
          ·
            refine ⟨1788327128785477042353521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4768872343427938779609389 1788327128785477042353521)
            ·
              refine ⟨1341245346589107781765141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788327128785477042353521 1341245346589107781765141)
              ·
                refine ⟨62870875621364427270241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1341245346589107781765141 62870875621364427270241)
                ·
                  rfl

theorem cell20_413237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_413237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413237 prefixEnd_413237 := by exact prefixLift 413237
  have htrace : WordTrace (prefixWord ++ tailWord_413237) baseStart_413237 baseEnd_413237 := by
    simpa [prefixWord, tailWord_413237, baseEnd_413237] using wordTrace_append hprefix tailTrace_413237
  have hstable : (prefixWord ++ tailWord_413237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413237).length < 2 ^ (prefixWord ++ tailWord_413237).sum := by decide
  have hdescent : baseEnd_413237 < baseStart_413237 := by decide
  rcases family_descends (prefixWord ++ tailWord_413237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413254 : List Nat := [6, 1, 1, 1, 11]
def baseStart_413254 : Nat := 118140960795 + 413254 * 2 ^ 59
def prefixEnd_413254 : Nat := 4983230072969 + 3 ^ 40 * 413254 * 2
def baseEnd_413254 : Nat := 2328646742312552817827

theorem tailTrace_413254 : CollatzResearch.WordTrace tailWord_413254 prefixEnd_413254 2328646742312552817827 := by
  unfold tailWord_413254
  simp only [CollatzResearch.WordTrace]
  refine ⟨471019113901837844040463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10048407763239207339529877 471019113901837844040463)
  ·
    refine ⟨706528670852756766060695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 471019113901837844040463 706528670852756766060695)
    ·
      refine ⟨1059793006279135149091043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706528670852756766060695 1059793006279135149091043)
      ·
        refine ⟨1589689509418702723636565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059793006279135149091043 1589689509418702723636565)
        ·
          refine ⟨2328646742312552817827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1589689509418702723636565 2328646742312552817827)
          ·
            rfl

theorem cell20_413254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 11].length) (baseStart_413254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413254 prefixEnd_413254 := by exact prefixLift 413254
  have htrace : WordTrace (prefixWord ++ tailWord_413254) baseStart_413254 baseEnd_413254 := by
    simpa [prefixWord, tailWord_413254, baseEnd_413254] using wordTrace_append hprefix tailTrace_413254
  have hstable : (prefixWord ++ tailWord_413254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413254).length < 2 ^ (prefixWord ++ tailWord_413254).sum := by decide
  have hdescent : baseEnd_413254 < baseStart_413254 := by decide
  rcases family_descends (prefixWord ++ tailWord_413254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413268 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_413268 : Nat := 118140960795 + 413268 * 2 ^ 59
def prefixEnd_413268 : Nat := 4983230072969 + 3 ^ 40 * 413268 * 2
def baseEnd_413268 : Nat := 188626776108794951777263

theorem tailTrace_413268 : CollatzResearch.WordTrace tailWord_413268 prefixEnd_413268 188626776108794951777263 := by
  unfold tailWord_413268
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536561133404045700152229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10048748177872060933536305 7536561133404045700152229)
  ·
    refine ⟨1413105212513258568778543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7536561133404045700152229 1413105212513258568778543)
    ·
      refine ⟨2119657818769887853167815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1413105212513258568778543 2119657818769887853167815)
      ·
        refine ⟨3179486728154831779751723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2119657818769887853167815 3179486728154831779751723)
        ·
          refine ⟨4769230092232247669627585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179486728154831779751723 4769230092232247669627585)
          ·
            refine ⟨3576922569174185752220689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4769230092232247669627585 3576922569174185752220689)
            ·
              refine ⟨2682691926880639314165517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576922569174185752220689 2682691926880639314165517)
              ·
                refine ⟨1006009472580239742812069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2682691926880639314165517 1006009472580239742812069)
                ·
                  refine ⟨188626776108794951777263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006009472580239742812069 188626776108794951777263)
                  ·
                    rfl

theorem cell20_413268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_413268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413268 prefixEnd_413268 := by exact prefixLift 413268
  have htrace : WordTrace (prefixWord ++ tailWord_413268) baseStart_413268 baseEnd_413268 := by
    simpa [prefixWord, tailWord_413268, baseEnd_413268] using wordTrace_append hprefix tailTrace_413268
  have hstable : (prefixWord ++ tailWord_413268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413268).length < 2 ^ (prefixWord ++ tailWord_413268).sum := by decide
  have hdescent : baseEnd_413268 < baseStart_413268 := by decide
  rcases family_descends (prefixWord ++ tailWord_413268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413289 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_413289 : Nat := 118140960795 + 413289 * 2 ^ 59
def prefixEnd_413289 : Nat := 4983230072969 + 3 ^ 40 * 413289 * 2
def baseEnd_413289 : Nat := 188636361081012212077177

theorem tailTrace_413289 : CollatzResearch.WordTrace tailWord_413289 prefixEnd_413289 188636361081012212077177 := by
  unfold tailWord_413289
  simp only [CollatzResearch.WordTrace]
  refine ⟨15073888199732011986818921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10049258799821341324545947 15073888199732011986818921)
  ·
    refine ⟨11305416149799008990114191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15073888199732011986818921 11305416149799008990114191)
    ·
      refine ⟨16958124224698513485171287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11305416149799008990114191 16958124224698513485171287)
      ·
        refine ⟨25437186337047770227756931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16958124224698513485171287 25437186337047770227756931)
        ·
          refine ⟨38155779505571655341635397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25437186337047770227756931 38155779505571655341635397)
          ·
            refine ⟨7154208657294685376556637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38155779505571655341635397 7154208657294685376556637)
            ·
              refine ⟨2682828246485507016208739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7154208657294685376556637 2682828246485507016208739)
              ·
                refine ⟨4024242369728260524313109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682828246485507016208739 4024242369728260524313109)
                ·
                  refine ⟨188636361081012212077177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4024242369728260524313109 188636361081012212077177)
                  ·
                    rfl

theorem cell20_413289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_413289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413289 prefixEnd_413289 := by exact prefixLift 413289
  have htrace : WordTrace (prefixWord ++ tailWord_413289) baseStart_413289 baseEnd_413289 := by
    simpa [prefixWord, tailWord_413289, baseEnd_413289] using wordTrace_append hprefix tailTrace_413289
  have hstable : (prefixWord ++ tailWord_413289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413289).length < 2 ^ (prefixWord ++ tailWord_413289).sum := by decide
  have hdescent : baseEnd_413289 < baseStart_413289 := by decide
  rcases family_descends (prefixWord ++ tailWord_413289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413302 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_413302 : Nat := 118140960795 + 413302 * 2 ^ 59
def prefixEnd_413302 : Nat := 4983230072969 + 3 ^ 40 * 413302 * 2
def baseEnd_413302 : Nat := 188642294635241944643791

theorem tailTrace_413302 : CollatzResearch.WordTrace tailWord_413302 prefixEnd_413302 188642294635241944643791 := by
  unfold tailWord_413302
  simp only [CollatzResearch.WordTrace]
  refine ⟨942147646792807200440135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10049574899123276804694773 942147646792807200440135)
  ·
    refine ⟨1413221470189210800660203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942147646792807200440135 1413221470189210800660203)
    ·
      refine ⟨2119832205283816200990305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1413221470189210800660203 2119832205283816200990305)
      ·
        refine ⟨1589874153962862150742729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2119832205283816200990305 1589874153962862150742729)
        ·
          refine ⟨1192405615472146613057047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589874153962862150742729 1192405615472146613057047)
          ·
            refine ⟨1788608423208219919585571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192405615472146613057047 1788608423208219919585571)
            ·
              refine ⟨2682912634812329879378357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788608423208219919585571 2682912634812329879378357)
              ·
                refine ⟨251523059513655926191721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2682912634812329879378357 251523059513655926191721)
                ·
                  refine ⟨188642294635241944643791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251523059513655926191721 188642294635241944643791)
                  ·
                    rfl

theorem cell20_413302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_413302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413302 prefixEnd_413302 := by exact prefixLift 413302
  have htrace : WordTrace (prefixWord ++ tailWord_413302) baseStart_413302 baseEnd_413302 := by
    simpa [prefixWord, tailWord_413302, baseEnd_413302] using wordTrace_append hprefix tailTrace_413302
  have hstable : (prefixWord ++ tailWord_413302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413302).length < 2 ^ (prefixWord ++ tailWord_413302).sum := by decide
  have hdescent : baseEnd_413302 < baseStart_413302 := by decide
  rcases family_descends (prefixWord ++ tailWord_413302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413313 : List Nat := [1, 2, 4, 2, 1, 3, 7]
def baseStart_413313 : Nat := 118140960795 + 413313 * 2 ^ 59
def prefixEnd_413313 : Nat := 4983230072969 + 3 ^ 40 * 413313 * 2
def baseEnd_413313 : Nat := 20960812814997199475231

theorem tailTrace_413313 : CollatzResearch.WordTrace tailWord_413313 prefixEnd_413313 20960812814997199475231 := by
  unfold tailWord_413313
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074763551645064085692593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10049842367763376057128395 15074763551645064085692593)
  ·
    refine ⟨11306072663733798064269445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15074763551645064085692593 11306072663733798064269445)
    ·
      refine ⟨2119888624450087137050521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11306072663733798064269445 2119888624450087137050521)
      ·
        refine ⟨1589916468337565352787891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2119888624450087137050521 1589916468337565352787891)
        ·
          refine ⟨2384874702506348029181837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589916468337565352787891 2384874702506348029181837)
          ·
            refine ⟨894328013439880510943189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2384874702506348029181837 894328013439880510943189)
            ·
              refine ⟨20960812814997199475231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 894328013439880510943189 20960812814997199475231)
              ·
                rfl

theorem cell20_413313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_413313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413313 prefixEnd_413313 := by exact prefixLift 413313
  have htrace : WordTrace (prefixWord ++ tailWord_413313) baseStart_413313 baseEnd_413313 := by
    simpa [prefixWord, tailWord_413313, baseEnd_413313] using wordTrace_append hprefix tailTrace_413313
  have hstable : (prefixWord ++ tailWord_413313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413313).length < 2 ^ (prefixWord ++ tailWord_413313).sum := by decide
  have hdescent : baseEnd_413313 < baseStart_413313 := by decide
  rcases family_descends (prefixWord ++ tailWord_413313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413344 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_413344 : Nat := 118140960795 + 413344 * 2 ^ 59
def prefixEnd_413344 : Nat := 4983230072969 + 3 ^ 40 * 413344 * 2
def baseEnd_413344 : Nat := 188661464579676465243619

theorem tailTrace_413344 : CollatzResearch.WordTrace tailWord_413344 prefixEnd_413344 188661464579676465243619 := by
  unfold tailWord_413344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537947107266378190035543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10050596143021837586714057 7537947107266378190035543)
  ·
    refine ⟨11306920660899567285053315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7537947107266378190035543 11306920660899567285053315)
    ·
      refine ⟨16960380991349350927579973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11306920660899567285053315 16960380991349350927579973)
      ·
        refine ⟨3180071435878003298921245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16960380991349350927579973 3180071435878003298921245)
        ·
          refine ⟨1192526788454251237095467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3180071435878003298921245 1192526788454251237095467)
          ·
            refine ⟨1788790182681376855643201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192526788454251237095467 1788790182681376855643201)
            ·
              refine ⟨1341592637011032641732401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788790182681376855643201 1341592637011032641732401)
              ·
                refine ⟨1006194477758274481299301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341592637011032641732401 1006194477758274481299301)
                ·
                  refine ⟨188661464579676465243619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006194477758274481299301 188661464579676465243619)
                  ·
                    rfl

theorem cell20_413344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_413344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413344 prefixEnd_413344 := by exact prefixLift 413344
  have htrace : WordTrace (prefixWord ++ tailWord_413344) baseStart_413344 baseEnd_413344 := by
    simpa [prefixWord, tailWord_413344, baseEnd_413344] using wordTrace_append hprefix tailTrace_413344
  have hstable : (prefixWord ++ tailWord_413344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413344).length < 2 ^ (prefixWord ++ tailWord_413344).sum := by decide
  have hdescent : baseEnd_413344 < baseStart_413344 := by decide
  rcases family_descends (prefixWord ++ tailWord_413344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413388 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 3]
def baseStart_413388 : Nat := 118140960795 + 413388 * 2 ^ 59
def prefixEnd_413388 : Nat := 4983230072969 + 3 ^ 40 * 413388 * 2
def baseEnd_413388 : Nat := 188681547378607867776773

theorem tailTrace_413388 : CollatzResearch.WordTrace tailWord_413388 prefixEnd_413388 188681547378607867776773 := by
  unfold tailWord_413388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538749513186675947336409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10051666017582234596448545 7538749513186675947336409)
  ·
    refine ⟨5654062134890006960502307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7538749513186675947336409 5654062134890006960502307)
    ·
      refine ⟨8481093202335010440753461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654062134890006960502307 8481093202335010440753461)
      ·
        refine ⟨795102487718907228820637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8481093202335010440753461 795102487718907228820637)
        ·
          refine ⟨298163432894590210807739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795102487718907228820637 298163432894590210807739)
          ·
            refine ⟨447245149341885316211609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298163432894590210807739 447245149341885316211609)
            ·
              refine ⟨335433862006413987158707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447245149341885316211609 335433862006413987158707)
              ·
                refine ⟨503150793009620980738061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335433862006413987158707 503150793009620980738061)
                ·
                  refine ⟨188681547378607867776773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503150793009620980738061 188681547378607867776773)
                  ·
                    rfl

theorem cell20_413388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_413388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_413388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_413388 prefixEnd_413388 := by exact prefixLift 413388
  have htrace : WordTrace (prefixWord ++ tailWord_413388) baseStart_413388 baseEnd_413388 := by
    simpa [prefixWord, tailWord_413388, baseEnd_413388] using wordTrace_append hprefix tailTrace_413388
  have hstable : (prefixWord ++ tailWord_413388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413388).length < 2 ^ (prefixWord ++ tailWord_413388).sum := by decide
  have hdescent : baseEnd_413388 < baseStart_413388 := by decide
  rcases family_descends (prefixWord ++ tailWord_413388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
