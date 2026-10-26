import V185TrunkScan23Chunk0488

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2892089 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2892089 : Nat := 118140960795 + 2892089 * 2 ^ 59
def prefixEnd_2892089 : Nat := 4983230072969 + 3 ^ 40 * 2892089 * 2
def baseEnd_2892089 : Nat := 1485031752581040422187031

theorem tailTrace_2892089 : CollatzResearch.WordTrace tailWord_2892089 prefixEnd_2892089 1485031752581040422187031 := by
  unfold tailWord_2892089
  simp only [CollatzResearch.WordTrace]
  refine ⟨105483151619462957322575321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70322101079641971548383547 105483151619462957322575321)
  ·
    refine ⟨79112363714597217991931491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105483151619462957322575321 79112363714597217991931491)
    ·
      refine ⟨118668545571895826987897237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79112363714597217991931491 118668545571895826987897237)
      ·
        refine ⟨5562588073682616890057683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118668545571895826987897237 5562588073682616890057683)
        ·
          refine ⟨8343882110523925335086525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5562588073682616890057683 8343882110523925335086525)
          ·
            refine ⟨3128955791446472000657447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8343882110523925335086525 3128955791446472000657447)
            ·
              refine ⟨4693433687169708000986171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128955791446472000657447 4693433687169708000986171)
              ·
                refine ⟨7040150530754562001479257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693433687169708000986171 7040150530754562001479257)
                ·
                  refine ⟨5280112898065921501109443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7040150530754562001479257 5280112898065921501109443)
                  ·
                    refine ⟨7920169347098882251664165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5280112898065921501109443 7920169347098882251664165)
                    ·
                      refine ⟨1485031752581040422187031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7920169347098882251664165 1485031752581040422187031)
                      ·
                        rfl

theorem cell23_2892089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2892089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892089 prefixEnd_2892089 := by exact prefixLift 2892089
  have htrace : WordTrace (prefixWord ++ tailWord_2892089) baseStart_2892089 baseEnd_2892089 := by
    simpa [prefixWord, tailWord_2892089, baseEnd_2892089] using wordTrace_append hprefix tailTrace_2892089
  have hstable : (prefixWord ++ tailWord_2892089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892089).length < 2 ^ (prefixWord ++ tailWord_2892089).sum := by decide
  have hdescent : baseEnd_2892089 < baseStart_2892089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892112 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 6]
def baseStart_2892112 : Nat := 118140960795 + 2892112 * 2 ^ 59
def prefixEnd_2892112 : Nat := 4983230072969 + 3 ^ 40 * 2892112 * 2
def baseEnd_2892112 : Nat := 165004840292899314688825

theorem tailTrace_2892112 : CollatzResearch.WordTrace tailWord_2892112 prefixEnd_2892112 165004840292899314688825 := by
  unfold tailWord_2892112
  simp only [CollatzResearch.WordTrace]
  refine ⟨52741995249189816125331295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70322660332253088167108393 52741995249189816125331295)
  ·
    refine ⟨79112992873784724187996943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52741995249189816125331295 79112992873784724187996943)
    ·
      refine ⟨118669489310677086281995415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79112992873784724187996943 118669489310677086281995415)
      ·
        refine ⟨178004233966015629422993123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118669489310677086281995415 178004233966015629422993123)
        ·
          refine ⟨267006350949023444134489685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178004233966015629422993123 267006350949023444134489685)
          ·
            refine ⟨3128980675183868485951051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 267006350949023444134489685 3128980675183868485951051)
            ·
              refine ⟨4693471012775802728926577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128980675183868485951051 4693471012775802728926577)
              ·
                refine ⟨3520103259581852046694933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693471012775802728926577 3520103259581852046694933)
                ·
                  refine ⟨165004840292899314688825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3520103259581852046694933 165004840292899314688825)
                  ·
                    rfl

theorem cell23_2892112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_2892112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892112 prefixEnd_2892112 := by exact prefixLift 2892112
  have htrace : WordTrace (prefixWord ++ tailWord_2892112) baseStart_2892112 baseEnd_2892112 := by
    simpa [prefixWord, tailWord_2892112, baseEnd_2892112] using wordTrace_append hprefix tailTrace_2892112
  have hstable : (prefixWord ++ tailWord_2892112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892112).length < 2 ^ (prefixWord ++ tailWord_2892112).sum := by decide
  have hdescent : baseEnd_2892112 < baseStart_2892112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892132 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_2892132 : Nat := 118140960795 + 2892132 * 2 ^ 59
def prefixEnd_2892132 : Nat := 4983230072969 + 3 ^ 40 * 2892132 * 2
def baseEnd_2892132 : Nat := 1485053832249183753949333

theorem tailTrace_2892132 : CollatzResearch.WordTrace tailWord_2892132 prefixEnd_2892132 1485053832249183753949333 := by
  unfold tailWord_2892132
  simp only [CollatzResearch.WordTrace]
  refine ⟨52742359979153587833195325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70323146638871450444260433 52742359979153587833195325)
  ·
    refine ⟨19778384992182595437448247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52742359979153587833195325 19778384992182595437448247)
    ·
      refine ⟨29667577488273893156172371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19778384992182595437448247 29667577488273893156172371)
      ·
        refine ⟨44501366232410839734258557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29667577488273893156172371 44501366232410839734258557)
        ·
          refine ⟨16688012337154064900346959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44501366232410839734258557 16688012337154064900346959)
          ·
            refine ⟨25032018505731097350520439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16688012337154064900346959 25032018505731097350520439)
            ·
              refine ⟨37548027758596646025780659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25032018505731097350520439 37548027758596646025780659)
              ·
                refine ⟨56322041637894969038670989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37548027758596646025780659 56322041637894969038670989)
                ·
                  refine ⟨21120765614210613389501621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56322041637894969038670989 21120765614210613389501621)
                  ·
                    refine ⟨1980071776332245005265777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21120765614210613389501621 1980071776332245005265777)
                    ·
                      refine ⟨1485053832249183753949333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980071776332245005265777 1485053832249183753949333)
                      ·
                        rfl

theorem cell23_2892132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_2892132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892132 prefixEnd_2892132 := by exact prefixLift 2892132
  have htrace : WordTrace (prefixWord ++ tailWord_2892132) baseStart_2892132 baseEnd_2892132 := by
    simpa [prefixWord, tailWord_2892132, baseEnd_2892132] using wordTrace_append hprefix tailTrace_2892132
  have hstable : (prefixWord ++ tailWord_2892132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892132).length < 2 ^ (prefixWord ++ tailWord_2892132).sum := by decide
  have hdescent : baseEnd_2892132 < baseStart_2892132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892149 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_2892149 : Nat := 118140960795 + 2892149 * 2 ^ 59
def prefixEnd_2892149 : Nat := 4983230072969 + 3 ^ 40 * 2892149 * 2
def baseEnd_2892149 : Nat := 1485062561420310187436755

theorem tailTrace_2892149 : CollatzResearch.WordTrace tailWord_2892149 prefixEnd_2892149 1485062561420310187436755 := by
  unfold tailWord_2892149
  simp only [CollatzResearch.WordTrace]
  refine ⟨105485339999245587569759501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70323559999497058379839667 105485339999245587569759501)
  ·
    refine ⟨39557002499717095338659813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105485339999245587569759501 39557002499717095338659813)
    ·
      refine ⟨7416937968696955375998715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39557002499717095338659813 7416937968696955375998715)
      ·
        refine ⟨11125406953045433063998073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7416937968696955375998715 11125406953045433063998073)
        ·
          refine ⟨8344055214784074797998555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11125406953045433063998073 8344055214784074797998555)
          ·
            refine ⟨12516082822176112196997833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8344055214784074797998555 12516082822176112196997833)
            ·
              refine ⟨9387062116632084147748375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12516082822176112196997833 9387062116632084147748375)
              ·
                refine ⟨14080593174948126221622563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387062116632084147748375 14080593174948126221622563)
                ·
                  refine ⟨21120889762422189332433845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14080593174948126221622563 21120889762422189332433845)
                  ·
                    refine ⟨1980083415227080249915673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21120889762422189332433845 1980083415227080249915673)
                    ·
                      refine ⟨1485062561420310187436755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980083415227080249915673 1485062561420310187436755)
                      ·
                        rfl

theorem cell23_2892149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_2892149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892149 prefixEnd_2892149 := by exact prefixLift 2892149
  have htrace : WordTrace (prefixWord ++ tailWord_2892149) baseStart_2892149 baseEnd_2892149 := by
    simpa [prefixWord, tailWord_2892149, baseEnd_2892149] using wordTrace_append hprefix tailTrace_2892149
  have hstable : (prefixWord ++ tailWord_2892149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892149).length < 2 ^ (prefixWord ++ tailWord_2892149).sum := by decide
  have hdescent : baseEnd_2892149 < baseStart_2892149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892150 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_2892150 : Nat := 118140960795 + 2892150 * 2 ^ 59
def prefixEnd_2892150 : Nat := 4983230072969 + 3 ^ 40 * 2892150 * 2
def baseEnd_2892150 : Nat := 495021024966988227841417

theorem tailTrace_2892150 : CollatzResearch.WordTrace tailWord_2892150 prefixEnd_2892150 495021024966988227841417 := by
  unfold tailWord_2892150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592836029515122796284119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70323584314827976493697269 6592836029515122796284119)
  ·
    refine ⟨9889254044272684194426179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592836029515122796284119 9889254044272684194426179)
    ·
      refine ⟨14833881066409026291639269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9889254044272684194426179 14833881066409026291639269)
      ·
        refine ⟨2781352699951692429682363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14833881066409026291639269 2781352699951692429682363)
        ·
          refine ⟨4172029049927538644523545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781352699951692429682363 4172029049927538644523545)
          ·
            refine ⟨3129021787445653983392659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4172029049927538644523545 3129021787445653983392659)
            ·
              refine ⟨4693532681168480975088989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129021787445653983392659 4693532681168480975088989)
              ·
                refine ⟨1760074755438180365658371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4693532681168480975088989 1760074755438180365658371)
                ·
                  refine ⟨2640112133157270548487557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760074755438180365658371 2640112133157270548487557)
                  ·
                    refine ⟨495021024966988227841417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640112133157270548487557 495021024966988227841417)
                    ·
                      rfl

theorem cell23_2892150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_2892150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892150 prefixEnd_2892150 := by exact prefixLift 2892150
  have htrace : WordTrace (prefixWord ++ tailWord_2892150) baseStart_2892150 baseEnd_2892150 := by
    simpa [prefixWord, tailWord_2892150, baseEnd_2892150] using wordTrace_append hprefix tailTrace_2892150
  have hstable : (prefixWord ++ tailWord_2892150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892150).length < 2 ^ (prefixWord ++ tailWord_2892150).sum := by decide
  have hdescent : baseEnd_2892150 < baseStart_2892150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892172 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_2892172 : Nat := 118140960795 + 2892172 * 2 ^ 59
def prefixEnd_2892172 : Nat := 4983230072969 + 3 ^ 40 * 2892172 * 2
def baseEnd_2892172 : Nat := 495024790491787865816383

theorem tailTrace_2892172 : CollatzResearch.WordTrace tailWord_2892172 prefixEnd_2892172 495024790491787865816383 := by
  unfold tailWord_2892172
  simp only [CollatzResearch.WordTrace]
  refine ⟨52743089439081131248923385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70324119252108174998564513 52743089439081131248923385)
  ·
    refine ⟨39557317079310848436692539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52743089439081131248923385 39557317079310848436692539)
    ·
      refine ⟨59335975618966272655038809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39557317079310848436692539 59335975618966272655038809)
      ·
        refine ⟨44501981714224704491279107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59335975618966272655038809 44501981714224704491279107)
        ·
          refine ⟨66752972571337056736918661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44501981714224704491279107 66752972571337056736918661)
          ·
            refine ⟨12516182357125698138172249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66752972571337056736918661 12516182357125698138172249)
            ·
              refine ⟨9387136767844273603629187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12516182357125698138172249 9387136767844273603629187)
              ·
                refine ⟨14080705151766410405443781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387136767844273603629187 14080705151766410405443781)
                ·
                  refine ⟨2640132215956201951020709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14080705151766410405443781 2640132215956201951020709)
                  ·
                    refine ⟨495024790491787865816383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640132215956201951020709 495024790491787865816383)
                    ·
                      rfl

theorem cell23_2892172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_2892172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892172 prefixEnd_2892172 := by exact prefixLift 2892172
  have htrace : WordTrace (prefixWord ++ tailWord_2892172) baseStart_2892172 baseEnd_2892172 := by
    simpa [prefixWord, tailWord_2892172, baseEnd_2892172] using wordTrace_append hprefix tailTrace_2892172
  have hstable : (prefixWord ++ tailWord_2892172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892172).length < 2 ^ (prefixWord ++ tailWord_2892172).sum := by decide
  have hdescent : baseEnd_2892172 < baseStart_2892172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892185 : List Nat := [1, 2, 1, 2, 1, 4, 4, 8]
def baseStart_2892185 : Nat := 118140960795 + 2892185 * 2 ^ 59
def prefixEnd_2892185 : Nat := 4983230072969 + 3 ^ 40 * 2892185 * 2
def baseEnd_2892185 : Nat := 55003001730513779503207

theorem tailTrace_2892185 : CollatzResearch.WordTrace tailWord_2892185 prefixEnd_2892185 55003001730513779503207 := by
  unfold tailWord_2892185
  simp only [CollatzResearch.WordTrace]
  refine ⟨105486653027115165718070009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70324435351410110478713339 105486653027115165718070009)
  ·
    refine ⟨79114989770336374288552507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105486653027115165718070009 79114989770336374288552507)
    ·
      refine ⟨118672484655504561432828761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79114989770336374288552507 118672484655504561432828761)
      ·
        refine ⟨89004363491628421074621571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118672484655504561432828761 89004363491628421074621571)
        ·
          refine ⟨133506545237442631611932357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89004363491628421074621571 133506545237442631611932357)
          ·
            refine ⟨25032477232020493427237317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133506545237442631611932357 25032477232020493427237317)
            ·
              refine ⟨4693589481003842517606997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25032477232020493427237317 4693589481003842517606997)
              ·
                refine ⟨55003001730513779503207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4693589481003842517606997 55003001730513779503207)
                ·
                  rfl

theorem cell23_2892185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 8].length) (baseStart_2892185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892185 prefixEnd_2892185 := by exact prefixLift 2892185
  have htrace : WordTrace (prefixWord ++ tailWord_2892185) baseStart_2892185 baseEnd_2892185 := by
    simpa [prefixWord, tailWord_2892185, baseEnd_2892185] using wordTrace_append hprefix tailTrace_2892185
  have hstable : (prefixWord ++ tailWord_2892185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892185).length < 2 ^ (prefixWord ++ tailWord_2892185).sum := by decide
  have hdescent : baseEnd_2892185 < baseStart_2892185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892193 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 1, 5]
def baseStart_2892193 : Nat := 118140960795 + 2892193 * 2 ^ 59
def prefixEnd_2892193 : Nat := 4983230072969 + 3 ^ 40 * 2892193 * 2
def baseEnd_2892193 : Nat := 495028384856369338428851

theorem tailTrace_2892193 : CollatzResearch.WordTrace tailWord_2892193 prefixEnd_2892193 495028384856369338428851 := by
  unfold tailWord_2892193
  simp only [CollatzResearch.WordTrace]
  refine ⟨105486944811086183084361233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70324629874057455389574155 105486944811086183084361233)
  ·
    refine ⟨79115208608314637313270925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105486944811086183084361233 79115208608314637313270925)
    ·
      refine ⟨29668203228117988992476597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79115208608314637313270925 29668203228117988992476597)
      ·
        refine ⟨2781394052636061468044681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29668203228117988992476597 2781394052636061468044681)
        ·
          refine ⟨2086045539477046101033511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781394052636061468044681 2086045539477046101033511)
          ·
            refine ⟨3129068309215569151550267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086045539477046101033511 3129068309215569151550267)
            ·
              refine ⟨4693602463823353727325401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129068309215569151550267 4693602463823353727325401)
              ·
                refine ⟨3520201847867515295494051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4693602463823353727325401 3520201847867515295494051)
                ·
                  refine ⟨5280302771801272943241077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3520201847867515295494051 5280302771801272943241077)
                  ·
                    refine ⟨495028384856369338428851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5280302771801272943241077 495028384856369338428851)
                    ·
                      rfl

theorem cell23_2892193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_2892193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892193 prefixEnd_2892193 := by exact prefixLift 2892193
  have htrace : WordTrace (prefixWord ++ tailWord_2892193) baseStart_2892193 baseEnd_2892193 := by
    simpa [prefixWord, tailWord_2892193, baseEnd_2892193] using wordTrace_append hprefix tailTrace_2892193
  have hstable : (prefixWord ++ tailWord_2892193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892193).length < 2 ^ (prefixWord ++ tailWord_2892193).sum := by decide
  have hdescent : baseEnd_2892193 < baseStart_2892193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892199 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2892199 : Nat := 118140960795 + 2892199 * 2 ^ 59
def prefixEnd_2892199 : Nat := 4983230072969 + 3 ^ 40 * 2892199 * 2
def baseEnd_2892199 : Nat := 1485088235453034991811525

theorem tailTrace_2892199 : CollatzResearch.WordTrace tailWord_2892199 prefixEnd_2892199 1485088235453034991811525 := by
  unfold tailWord_2892199
  simp only [CollatzResearch.WordTrace]
  refine ⟨105487163649064446109079651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70324775766042964072719767 105487163649064446109079651)
  ·
    refine ⟨158230745473596669163619477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105487163649064446109079651 158230745473596669163619477)
    ·
      refine ⟨7417066194074843867044663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158230745473596669163619477 7417066194074843867044663)
      ·
        refine ⟨11125599291112265800566995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417066194074843867044663 11125599291112265800566995)
        ·
          refine ⟨16688398936668398700850493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125599291112265800566995 16688398936668398700850493)
          ·
            refine ⟨6258149601250649512818935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16688398936668398700850493 6258149601250649512818935)
            ·
              refine ⟨9387224401875974269228403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258149601250649512818935 9387224401875974269228403)
              ·
                refine ⟨14080836602813961403842605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387224401875974269228403 14080836602813961403842605)
                ·
                  refine ⟨5280313726055235526440977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14080836602813961403842605 5280313726055235526440977)
                  ·
                    refine ⟨3960235294541426644830733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5280313726055235526440977 3960235294541426644830733)
                    ·
                      refine ⟨1485088235453034991811525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3960235294541426644830733 1485088235453034991811525)
                      ·
                        rfl

theorem cell23_2892199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2892199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892199 prefixEnd_2892199 := by exact prefixLift 2892199
  have htrace : WordTrace (prefixWord ++ tailWord_2892199) baseStart_2892199 baseEnd_2892199 := by
    simpa [prefixWord, tailWord_2892199, baseEnd_2892199] using wordTrace_append hprefix tailTrace_2892199
  have hstable : (prefixWord ++ tailWord_2892199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892199).length < 2 ^ (prefixWord ++ tailWord_2892199).sum := by decide
  have hdescent : baseEnd_2892199 < baseStart_2892199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892246 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2892246 : Nat := 118140960795 + 2892246 * 2 ^ 59
def prefixEnd_2892246 : Nat := 4983230072969 + 3 ^ 40 * 2892246 * 2
def baseEnd_2892246 : Nat := 1485112369043796307923809

theorem tailTrace_2892246 : CollatzResearch.WordTrace tailWord_2892246 prefixEnd_2892246 1485112369043796307923809 := by
  unfold tailWord_2892246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6593054867493385821002537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70325918586596115424027061 6593054867493385821002537)
  ·
    refine ⟨4944791150620039365751903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6593054867493385821002537 4944791150620039365751903)
    ·
      refine ⟨7417186725930059048627855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944791150620039365751903 7417186725930059048627855)
      ·
        refine ⟨11125780088895088572941783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417186725930059048627855 11125780088895088572941783)
        ·
          refine ⟨16688670133342632859412675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125780088895088572941783 16688670133342632859412675)
          ·
            refine ⟨25033005200013949289119013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16688670133342632859412675 25033005200013949289119013)
            ·
              refine ⟨4693688475002615491709815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25033005200013949289119013 4693688475002615491709815)
              ·
                refine ⟨7040532712503923237564723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693688475002615491709815 7040532712503923237564723)
                ·
                  refine ⟨10560799068755884856347085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7040532712503923237564723 10560799068755884856347085)
                  ·
                    refine ⟨3960299650783456821130157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10560799068755884856347085 3960299650783456821130157)
                    ·
                      refine ⟨1485112369043796307923809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3960299650783456821130157 1485112369043796307923809)
                      ·
                        rfl

theorem cell23_2892246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2892246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892246 prefixEnd_2892246 := by exact prefixLift 2892246
  have htrace : WordTrace (prefixWord ++ tailWord_2892246) baseStart_2892246 baseEnd_2892246 := by
    simpa [prefixWord, tailWord_2892246, baseEnd_2892246] using wordTrace_append hprefix tailTrace_2892246
  have hstable : (prefixWord ++ tailWord_2892246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892246).length < 2 ^ (prefixWord ++ tailWord_2892246).sum := by decide
  have hdescent : baseEnd_2892246 < baseStart_2892246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892275 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 9]
def baseStart_2892275 : Nat := 118140960795 + 2892275 * 2 ^ 59
def prefixEnd_2892275 : Nat := 4983230072969 + 3 ^ 40 * 2892275 * 2
def baseEnd_2892275 : Nat := 165014139998086299384575

theorem tailTrace_2892275 : CollatzResearch.WordTrace tailWord_2892275 prefixEnd_2892275 165014139998086299384575 := by
  unfold tailWord_2892275
  simp only [CollatzResearch.WordTrace]
  refine ⟨105489935596789111088846279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70326623731192740725897519 105489935596789111088846279)
  ·
    refine ⟨158234903395183666633269419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105489935596789111088846279 158234903395183666633269419)
    ·
      refine ⟨237352355092775499949904129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158234903395183666633269419 237352355092775499949904129)
      ·
        refine ⟨178014266319581624962428097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237352355092775499949904129 178014266319581624962428097)
        ·
          refine ⟨133510699739686218721821073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178014266319581624962428097 133510699739686218721821073)
          ·
            refine ⟨100133024804764664041365805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133510699739686218721821073 100133024804764664041365805)
            ·
              refine ⟨37549884301786749015512177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100133024804764664041365805 37549884301786749015512177)
              ·
                refine ⟨28162413226340061761634133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37549884301786749015512177 28162413226340061761634133)
                ·
                  refine ⟨165014139998086299384575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28162413226340061761634133 165014139998086299384575)
                  ·
                    rfl

theorem cell23_2892275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 9].length) (baseStart_2892275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892275 prefixEnd_2892275 := by exact prefixLift 2892275
  have htrace : WordTrace (prefixWord ++ tailWord_2892275) baseStart_2892275 baseEnd_2892275 := by
    simpa [prefixWord, tailWord_2892275, baseEnd_2892275] using wordTrace_append hprefix tailTrace_2892275
  have hstable : (prefixWord ++ tailWord_2892275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892275).length < 2 ^ (prefixWord ++ tailWord_2892275).sum := by decide
  have hdescent : baseEnd_2892275 < baseStart_2892275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892349 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2892349 : Nat := 118140960795 + 2892349 * 2 ^ 59
def prefixEnd_2892349 : Nat := 4983230072969 + 3 ^ 40 * 2892349 * 2
def baseEnd_2892349 : Nat := 1485165257551209404935835

theorem tailTrace_2892349 : CollatzResearch.WordTrace tailWord_2892349 prefixEnd_2892349 1485165257551209404935835 := by
  unfold tailWord_2892349
  simp only [CollatzResearch.WordTrace]
  refine ⟨105492634598521021727040101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70328423065680681151360067 105492634598521021727040101)
  ·
    refine ⟨19779868987222691573820019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105492634598521021727040101 19779868987222691573820019)
    ·
      refine ⟨29669803480834037360730029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19779868987222691573820019 29669803480834037360730029)
      ·
        refine ⟨11126176305312764010273761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29669803480834037360730029 11126176305312764010273761)
        ·
          refine ⟨8344632228984573007705321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11126176305312764010273761 8344632228984573007705321)
          ·
            refine ⟨6258474171738429755778991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8344632228984573007705321 6258474171738429755778991)
            ·
              refine ⟨9387711257607644633668487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258474171738429755778991 9387711257607644633668487)
              ·
                refine ⟨14081566886411466950502731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9387711257607644633668487 14081566886411466950502731)
                ·
                  refine ⟨21122350329617200425754097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14081566886411466950502731 21122350329617200425754097)
                  ·
                    refine ⟨15841762747212900319315573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21122350329617200425754097 15841762747212900319315573)
                    ·
                      refine ⟨1485165257551209404935835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15841762747212900319315573 1485165257551209404935835)
                      ·
                        rfl

theorem cell23_2892349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2892349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892349 prefixEnd_2892349 := by exact prefixLift 2892349
  have htrace : WordTrace (prefixWord ++ tailWord_2892349) baseStart_2892349 baseEnd_2892349 := by
    simpa [prefixWord, tailWord_2892349, baseEnd_2892349] using wordTrace_append hprefix tailTrace_2892349
  have hstable : (prefixWord ++ tailWord_2892349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892349).length < 2 ^ (prefixWord ++ tailWord_2892349).sum := by decide
  have hdescent : baseEnd_2892349 < baseStart_2892349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892479 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_2892479 : Nat := 118140960795 + 2892479 * 2 ^ 59
def prefixEnd_2892479 : Nat := 4983230072969 + 3 ^ 40 * 2892479 * 2
def baseEnd_2892479 : Nat := 1485232010036293896310237

theorem tailTrace_2892479 : CollatzResearch.WordTrace tailWord_2892479 prefixEnd_2892479 1485232010036293896310237 := by
  unfold tailWord_2892479
  simp only [CollatzResearch.WordTrace]
  refine ⟨105497376088050053929272491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70331584058700035952848327 105497376088050053929272491)
  ·
    refine ⟨158246064132075080893908737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105497376088050053929272491 158246064132075080893908737)
    ·
      refine ⟨118684548099056310670431553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158246064132075080893908737 118684548099056310670431553)
      ·
        refine ⟨89013411074292233002823665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118684548099056310670431553 89013411074292233002823665)
        ·
          refine ⟨66760058305719174752117749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89013411074292233002823665 66760058305719174752117749)
          ·
            refine ⟨6258755466161172633011039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66760058305719174752117749 6258755466161172633011039)
            ·
              refine ⟨9388133199241758949516559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6258755466161172633011039 9388133199241758949516559)
              ·
                refine ⟨14082199798862638424274839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9388133199241758949516559 14082199798862638424274839)
                ·
                  refine ⟨21123299698293957636412259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14082199798862638424274839 21123299698293957636412259)
                  ·
                    refine ⟨31684949547440936454618389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21123299698293957636412259 31684949547440936454618389)
                    ·
                      refine ⟨1485232010036293896310237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31684949547440936454618389 1485232010036293896310237)
                      ·
                        rfl

theorem cell23_2892479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_2892479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892479 prefixEnd_2892479 := by exact prefixLift 2892479
  have htrace : WordTrace (prefixWord ++ tailWord_2892479) baseStart_2892479 baseEnd_2892479 := by
    simpa [prefixWord, tailWord_2892479, baseEnd_2892479] using wordTrace_append hprefix tailTrace_2892479
  have hstable : (prefixWord ++ tailWord_2892479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892479).length < 2 ^ (prefixWord ++ tailWord_2892479).sum := by decide
  have hdescent : baseEnd_2892479 < baseStart_2892479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892559 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_2892559 : Nat := 118140960795 + 2892559 * 2 ^ 59
def prefixEnd_2892559 : Nat := 4983230072969 + 3 ^ 40 * 2892559 * 2
def baseEnd_2892559 : Nat := 1485273088488653583309869

theorem tailTrace_2892559 : CollatzResearch.WordTrace tailWord_2892559 prefixEnd_2892559 1485273088488653583309869 := by
  unfold tailWord_2892559
  simp only [CollatzResearch.WordTrace]
  refine ⟨105500293927760227592184731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70333529285173485061456487 105500293927760227592184731)
  ·
    refine ⟨158250440891640341388277097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105500293927760227592184731 158250440891640341388277097)
    ·
      refine ⟨118687830668730256041207823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158250440891640341388277097 118687830668730256041207823)
      ·
        refine ⟨178031746003095384061811735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118687830668730256041207823 178031746003095384061811735)
        ·
          refine ⟨267047619004643076092717603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178031746003095384061811735 267047619004643076092717603)
          ·
            refine ⟨400571428506964614139076405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267047619004643076092717603 400571428506964614139076405)
            ·
              refine ⟨37553571422527932575538413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 400571428506964614139076405 37553571422527932575538413)
              ·
                refine ⟨14082589283447974715826905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37553571422527932575538413 14082589283447974715826905)
                ·
                  refine ⟨10561941962585981036870179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14082589283447974715826905 10561941962585981036870179)
                  ·
                    refine ⟨15842912943878971555305269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10561941962585981036870179 15842912943878971555305269)
                    ·
                      refine ⟨1485273088488653583309869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15842912943878971555305269 1485273088488653583309869)
                      ·
                        rfl

theorem cell23_2892559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_2892559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892559 prefixEnd_2892559 := by exact prefixLift 2892559
  have htrace : WordTrace (prefixWord ++ tailWord_2892559) baseStart_2892559 baseEnd_2892559 := by
    simpa [prefixWord, tailWord_2892559, baseEnd_2892559] using wordTrace_append hprefix tailTrace_2892559
  have hstable : (prefixWord ++ tailWord_2892559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892559).length < 2 ^ (prefixWord ++ tailWord_2892559).sum := by decide
  have hdescent : baseEnd_2892559 < baseStart_2892559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892576 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2892576 : Nat := 118140960795 + 2892576 * 2 ^ 59
def prefixEnd_2892576 : Nat := 4983230072969 + 3 ^ 40 * 2892576 * 2
def baseEnd_2892576 : Nat := 1485281817659780016797291

theorem tailTrace_2892576 : CollatzResearch.WordTrace tailWord_2892576 prefixEnd_2892576 1485281817659780016797291 := by
  unfold tailWord_2892576
  simp only [CollatzResearch.WordTrace]
  refine ⟨52750456984349319747776791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70333942645799092997035721 52750456984349319747776791)
  ·
    refine ⟨79125685476523979621665187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52750456984349319747776791 79125685476523979621665187)
    ·
      refine ⟨118688528214785969432497781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79125685476523979621665187 118688528214785969432497781)
      ·
        refine ⟨11127049520136184634296667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118688528214785969432497781 11127049520136184634296667)
        ·
          refine ⟨16690574280204276951445001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11127049520136184634296667 16690574280204276951445001)
          ·
            refine ⟨12517930710153207713583751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16690574280204276951445001 12517930710153207713583751)
            ·
              refine ⟨18776896065229811570375627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12517930710153207713583751 18776896065229811570375627)
              ·
                refine ⟨28165344097844717355563441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18776896065229811570375627 28165344097844717355563441)
                ·
                  refine ⟨21124008073383538016672581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28165344097844717355563441 21124008073383538016672581)
                  ·
                    refine ⟨3960751513759413378126109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21124008073383538016672581 3960751513759413378126109)
                    ·
                      refine ⟨1485281817659780016797291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3960751513759413378126109 1485281817659780016797291)
                      ·
                        rfl

theorem cell23_2892576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2892576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892576 prefixEnd_2892576 := by exact prefixLift 2892576
  have htrace : WordTrace (prefixWord ++ tailWord_2892576) baseStart_2892576 baseEnd_2892576 := by
    simpa [prefixWord, tailWord_2892576, baseEnd_2892576] using wordTrace_append hprefix tailTrace_2892576
  have hstable : (prefixWord ++ tailWord_2892576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892576).length < 2 ^ (prefixWord ++ tailWord_2892576).sum := by decide
  have hdescent : baseEnd_2892576 < baseStart_2892576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892579 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 7]
def baseStart_2892579 : Nat := 118140960795 + 2892579 * 2 ^ 59
def prefixEnd_2892579 : Nat := 4983230072969 + 3 ^ 40 * 2892579 * 2
def baseEnd_2892579 : Nat := 165031484233527056117753

theorem tailTrace_2892579 : CollatzResearch.WordTrace tailWord_2892579 prefixEnd_2892579 165031484233527056117753 := by
  unfold tailWord_2892579
  simp only [CollatzResearch.WordTrace]
  refine ⟨105501023387687771007912791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70334015591791847338608527 105501023387687771007912791)
  ·
    refine ⟨158251535081531656511869187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105501023387687771007912791 158251535081531656511869187)
    ·
      refine ⟨237377302622297484767803781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158251535081531656511869187 237377302622297484767803781)
      ·
        refine ⟨44508244241680778393963209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237377302622297484767803781 44508244241680778393963209)
        ·
          refine ⟨33381183181260583795472407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44508244241680778393963209 33381183181260583795472407)
          ·
            refine ⟨50071774771890875693208611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33381183181260583795472407 50071774771890875693208611)
            ·
              refine ⟨75107662157836313539812917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50071774771890875693208611 75107662157836313539812917)
              ·
                refine ⟨7041343327297154394357461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75107662157836313539812917 7041343327297154394357461)
                ·
                  refine ⟨165031484233527056117753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7041343327297154394357461 165031484233527056117753)
                  ·
                    rfl

theorem cell23_2892579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 7].length) (baseStart_2892579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892579 prefixEnd_2892579 := by exact prefixLift 2892579
  have htrace : WordTrace (prefixWord ++ tailWord_2892579) baseStart_2892579 baseEnd_2892579 := by
    simpa [prefixWord, tailWord_2892579, baseEnd_2892579] using wordTrace_append hprefix tailTrace_2892579
  have hstable : (prefixWord ++ tailWord_2892579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892579).length < 2 ^ (prefixWord ++ tailWord_2892579).sum := by decide
  have hdescent : baseEnd_2892579 < baseStart_2892579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892590 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2892590 : Nat := 118140960795 + 2892590 * 2 ^ 59
def prefixEnd_2892590 : Nat := 4983230072969 + 3 ^ 40 * 2892590 * 2
def baseEnd_2892590 : Nat := 1485289006388942962022227

theorem tailTrace_2892590 : CollatzResearch.WordTrace tailWord_2892590 prefixEnd_2892590 1485289006388942962022227 := by
  unfold tailWord_2892590
  simp only [CollatzResearch.WordTrace]
  refine ⟨13187678073830989985820403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70334283060431946591042149 13187678073830989985820403)
  ·
    refine ⟨19781517110746484978730605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13187678073830989985820403 19781517110746484978730605)
    ·
      refine ⟨7418068916529931867023977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19781517110746484978730605 7418068916529931867023977)
      ·
        refine ⟨5563551687397448900267983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7418068916529931867023977 5563551687397448900267983)
        ·
          refine ⟨8345327531096173350401975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563551687397448900267983 8345327531096173350401975)
          ·
            refine ⟨12517991296644260025602963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345327531096173350401975 12517991296644260025602963)
            ·
              refine ⟨18776986944966390038404445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12517991296644260025602963 18776986944966390038404445)
              ·
                refine ⟨7041370104362396264401667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18776986944966390038404445 7041370104362396264401667)
                ·
                  refine ⟨10562055156543594396602501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041370104362396264401667 10562055156543594396602501)
                  ·
                    refine ⟨1980385341851923949362969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10562055156543594396602501 1980385341851923949362969)
                    ·
                      refine ⟨1485289006388942962022227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980385341851923949362969 1485289006388942962022227)
                      ·
                        rfl

theorem cell23_2892590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2892590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892590 prefixEnd_2892590 := by exact prefixLift 2892590
  have htrace : WordTrace (prefixWord ++ tailWord_2892590) baseStart_2892590 baseEnd_2892590 := by
    simpa [prefixWord, tailWord_2892590, baseEnd_2892590] using wordTrace_append hprefix tailTrace_2892590
  have hstable : (prefixWord ++ tailWord_2892590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892590).length < 2 ^ (prefixWord ++ tailWord_2892590).sum := by decide
  have hdescent : baseEnd_2892590 < baseStart_2892590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892626 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_2892626 : Nat := 118140960795 + 2892626 * 2 ^ 59
def prefixEnd_2892626 : Nat := 4983230072969 + 3 ^ 40 * 2892626 * 2
def baseEnd_2892626 : Nat := 495102497230834940390687

theorem tailTrace_2892626 : CollatzResearch.WordTrace tailWord_2892626 prefixEnd_2892626 495102497230834940390687 := by
  unfold tailWord_2892626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26375684404629374508718433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70335158412344998689915821 26375684404629374508718433)
  ·
    refine ⟨19781763303472030881538825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26375684404629374508718433 19781763303472030881538825)
    ·
      refine ⟨14836322477604023161154119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19781763303472030881538825 14836322477604023161154119)
      ·
        refine ⟨22254483716406034741731179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14836322477604023161154119 22254483716406034741731179)
        ·
          refine ⟨33381725574609052112596769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22254483716406034741731179 33381725574609052112596769)
          ·
            refine ⟨25036294180956789084447577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33381725574609052112596769 25036294180956789084447577)
            ·
              refine ⟨18777220635717591813335683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25036294180956789084447577 18777220635717591813335683)
              ·
                refine ⟨28165830953576387720003525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18777220635717591813335683 28165830953576387720003525)
                ·
                  refine ⟨5281093303795572697500661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28165830953576387720003525 5281093303795572697500661)
                  ·
                    refine ⟨495102497230834940390687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5281093303795572697500661 495102497230834940390687)
                    ·
                      rfl

theorem cell23_2892626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_2892626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892626 prefixEnd_2892626 := by exact prefixLift 2892626
  have htrace : WordTrace (prefixWord ++ tailWord_2892626) baseStart_2892626 baseEnd_2892626 := by
    simpa [prefixWord, tailWord_2892626, baseEnd_2892626] using wordTrace_append hprefix tailTrace_2892626
  have hstable : (prefixWord ++ tailWord_2892626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892626).length < 2 ^ (prefixWord ++ tailWord_2892626).sum := by decide
  have hdescent : baseEnd_2892626 < baseStart_2892626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892703 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 6]
def baseStart_2892703 : Nat := 118140960795 + 2892703 * 2 ^ 59
def prefixEnd_2892703 : Nat := 4983230072969 + 3 ^ 40 * 2892703 * 2
def baseEnd_2892703 : Nat := 165038558855877891101023

theorem tailTrace_2892703 : CollatzResearch.WordTrace tailWord_2892703 prefixEnd_2892703 165038558855877891101023 := by
  unfold tailWord_2892703
  simp only [CollatzResearch.WordTrace]
  refine ⟨105505546039238540185426763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70337030692825693456951175 105505546039238540185426763)
  ·
    refine ⟨158258319058857810278140145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105505546039238540185426763 158258319058857810278140145)
    ·
      refine ⟨118693739294143357708605109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158258319058857810278140145 118693739294143357708605109)
      ·
        refine ⟨11127538058825939785181729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118693739294143357708605109 11127538058825939785181729)
        ·
          refine ⟨8345653544119454838886297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11127538058825939785181729 8345653544119454838886297)
          ·
            refine ⟨6259240158089591129164723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8345653544119454838886297 6259240158089591129164723)
            ·
              refine ⟨9388860237134386693747085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259240158089591129164723 9388860237134386693747085)
              ·
                refine ⟨3520822588925395010155157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9388860237134386693747085 3520822588925395010155157)
                ·
                  refine ⟨165038558855877891101023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3520822588925395010155157 165038558855877891101023)
                  ·
                    rfl

theorem cell23_2892703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 6].length) (baseStart_2892703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892703 prefixEnd_2892703 := by exact prefixLift 2892703
  have htrace : WordTrace (prefixWord ++ tailWord_2892703) baseStart_2892703 baseEnd_2892703 := by
    simpa [prefixWord, tailWord_2892703, baseEnd_2892703] using wordTrace_append hprefix tailTrace_2892703
  have hstable : (prefixWord ++ tailWord_2892703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892703).length < 2 ^ (prefixWord ++ tailWord_2892703).sum := by decide
  have hdescent : baseEnd_2892703 < baseStart_2892703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892713 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 3]
def baseStart_2892713 : Nat := 118140960795 + 2892713 * 2 ^ 59
def prefixEnd_2892713 : Nat := 4983230072969 + 3 ^ 40 * 2892713 * 2
def baseEnd_2892713 : Nat := 1485352164509445980784161

theorem tailTrace_2892713 : CollatzResearch.WordTrace tailWord_2892713 prefixEnd_2892713 1485352164509445980784161 := by
  unfold tailWord_2892713
  simp only [CollatzResearch.WordTrace]
  refine ⟨105505910769202311893290793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70337273846134874595527195 105505910769202311893290793)
  ·
    refine ⟨79129433076901733919968095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105505910769202311893290793 79129433076901733919968095)
    ·
      refine ⟨118694149615352600879952143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79129433076901733919968095 118694149615352600879952143)
      ·
        refine ⟨178041224423028901319928215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118694149615352600879952143 178041224423028901319928215)
        ·
          refine ⟨267061836634543351979892323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178041224423028901319928215 267061836634543351979892323)
          ·
            refine ⟨400592754951815027969838485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267061836634543351979892323 400592754951815027969838485)
            ·
              refine ⟨18777785388366329436086179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 400592754951815027969838485 18777785388366329436086179)
              ·
                refine ⟨28166678082549494154129269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18777785388366329436086179 28166678082549494154129269)
                ·
                  refine ⟨2640626070239015076949619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28166678082549494154129269 2640626070239015076949619)
                  ·
                    refine ⟨3960939105358522615424429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2640626070239015076949619 3960939105358522615424429)
                    ·
                      refine ⟨1485352164509445980784161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3960939105358522615424429 1485352164509445980784161)
                      ·
                        rfl

theorem cell23_2892713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_2892713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892713 prefixEnd_2892713 := by exact prefixLift 2892713
  have htrace : WordTrace (prefixWord ++ tailWord_2892713) baseStart_2892713 baseEnd_2892713 := by
    simpa [prefixWord, tailWord_2892713, baseEnd_2892713] using wordTrace_append hprefix tailTrace_2892713
  have hstable : (prefixWord ++ tailWord_2892713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892713).length < 2 ^ (prefixWord ++ tailWord_2892713).sum := by decide
  have hdescent : baseEnd_2892713 < baseStart_2892713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892716 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_2892716 : Nat := 118140960795 + 2892716 * 2 ^ 59
def prefixEnd_2892716 : Nat := 4983230072969 + 3 ^ 40 * 2892716 * 2
def baseEnd_2892716 : Nat := 495117901650469823015549

theorem tailTrace_2892716 : CollatzResearch.WordTrace tailWord_2892716 prefixEnd_2892716 495117901650469823015549 := by
  unfold tailWord_2892716
  simp only [CollatzResearch.WordTrace]
  refine ⟨52753010094095721702825001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70337346792127628937100001 52753010094095721702825001)
  ·
    refine ⟨39564757570571791277118751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52753010094095721702825001 39564757570571791277118751)
    ·
      refine ⟨59347136355857686915678127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39564757570571791277118751 59347136355857686915678127)
      ·
        refine ⟨89020704533786530373517191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59347136355857686915678127 89020704533786530373517191)
        ·
          refine ⟨133531056800679795560275787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89020704533786530373517191 133531056800679795560275787)
          ·
            refine ⟨200296585201019693340413681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133531056800679795560275787 200296585201019693340413681)
            ·
              refine ⟨150222438900764770005310261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200296585201019693340413681 150222438900764770005310261)
              ·
                refine ⟨14083353646946697187997837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150222438900764770005310261 14083353646946697187997837)
                ·
                  refine ⟨5281257617605011445499189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14083353646946697187997837 5281257617605011445499189)
                  ·
                    refine ⟨495117901650469823015549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5281257617605011445499189 495117901650469823015549)
                    ·
                      rfl

theorem cell23_2892716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_2892716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892716 prefixEnd_2892716 := by exact prefixLift 2892716
  have htrace : WordTrace (prefixWord ++ tailWord_2892716) baseStart_2892716 baseEnd_2892716 := by
    simpa [prefixWord, tailWord_2892716, baseEnd_2892716] using wordTrace_append hprefix tailTrace_2892716
  have hstable : (prefixWord ++ tailWord_2892716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892716).length < 2 ^ (prefixWord ++ tailWord_2892716).sum := by decide
  have hdescent : baseEnd_2892716 < baseStart_2892716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892746 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_2892746 : Nat := 118140960795 + 2892746 * 2 ^ 59
def prefixEnd_2892746 : Nat := 4983230072969 + 3 ^ 40 * 2892746 * 2
def baseEnd_2892746 : Nat := 495123036457014783890503

theorem tailTrace_2892746 : CollatzResearch.WordTrace tailWord_2892746 prefixEnd_2892746 495123036457014783890503 := by
  unfold tailWord_2892746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26376778594520689632310523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70338076252055172352828061 26376778594520689632310523)
  ·
    refine ⟨39565167891781034448465785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26376778594520689632310523 39565167891781034448465785)
    ·
      refine ⟨29673875918835775836349339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39565167891781034448465785 29673875918835775836349339)
      ·
        refine ⟨44510813878253663754524009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29673875918835775836349339 44510813878253663754524009)
        ·
          refine ⟨33383110408690247815893007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44510813878253663754524009 33383110408690247815893007)
          ·
            refine ⟨50074665613035371723839511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33383110408690247815893007 50074665613035371723839511)
            ·
              refine ⟨75111998419553057585759267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50074665613035371723839511 75111998419553057585759267)
              ·
                refine ⟨112667997629329586378638901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75111998419553057585759267 112667997629329586378638901)
                ·
                  refine ⟨10562624777749648722997397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112667997629329586378638901 10562624777749648722997397)
                  ·
                    refine ⟨495123036457014783890503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10562624777749648722997397 495123036457014783890503)
                    ·
                      rfl

theorem cell23_2892746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_2892746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892746 prefixEnd_2892746 := by exact prefixLift 2892746
  have htrace : WordTrace (prefixWord ++ tailWord_2892746) baseStart_2892746 baseEnd_2892746 := by
    simpa [prefixWord, tailWord_2892746, baseEnd_2892746] using wordTrace_append hprefix tailTrace_2892746
  have hstable : (prefixWord ++ tailWord_2892746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892746).length < 2 ^ (prefixWord ++ tailWord_2892746).sum := by decide
  have hdescent : baseEnd_2892746 < baseStart_2892746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892747 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 1, 1, 3]
def baseStart_2892747 : Nat := 118140960795 + 2892747 * 2 ^ 59
def prefixEnd_2892747 : Nat := 4983230072969 + 3 ^ 40 * 2892747 * 2
def baseEnd_2892747 : Nat := 1485369622851698847759005

theorem tailTrace_2892747 : CollatzResearch.WordTrace tailWord_2892747 prefixEnd_2892747 1485369622851698847759005 := by
  unfold tailWord_2892747
  simp only [CollatzResearch.WordTrace]
  refine ⟨105507150851079135700028495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70338100567386090466685663 105507150851079135700028495)
  ·
    refine ⟨158260726276618703550042743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105507150851079135700028495 158260726276618703550042743)
    ·
      refine ⟨237391089414928055325064115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158260726276618703550042743 237391089414928055325064115)
      ·
        refine ⟨356086634122392082987596173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237391089414928055325064115 356086634122392082987596173)
        ·
          refine ⟨133532487795897031120348565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356086634122392082987596173 133532487795897031120348565)
          ·
            refine ⟨6259335365432673333766339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133532487795897031120348565 6259335365432673333766339)
            ·
              refine ⟨9389003048149010000649509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6259335365432673333766339 9389003048149010000649509)
              ·
                refine ⟨1760438071527939375121783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9389003048149010000649509 1760438071527939375121783)
                ·
                  refine ⟨2640657107291909062682675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760438071527939375121783 2640657107291909062682675)
                  ·
                    refine ⟨3960985660937863594024013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2640657107291909062682675 3960985660937863594024013)
                    ·
                      refine ⟨1485369622851698847759005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3960985660937863594024013 1485369622851698847759005)
                      ·
                        rfl

theorem cell23_2892747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 1, 3].length) (baseStart_2892747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892747 prefixEnd_2892747 := by exact prefixLift 2892747
  have htrace : WordTrace (prefixWord ++ tailWord_2892747) baseStart_2892747 baseEnd_2892747 := by
    simpa [prefixWord, tailWord_2892747, baseEnd_2892747] using wordTrace_append hprefix tailTrace_2892747
  have hstable : (prefixWord ++ tailWord_2892747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892747).length < 2 ^ (prefixWord ++ tailWord_2892747).sum := by decide
  have hdescent : baseEnd_2892747 < baseStart_2892747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892776 : List Nat := [2, 1, 4, 1, 1, 1, 2, 11]
def baseStart_2892776 : Nat := 118140960795 + 2892776 * 2 ^ 59
def prefixEnd_2892776 : Nat := 4983230072969 + 3 ^ 40 * 2892776 * 2
def baseEnd_2892776 : Nat := 55014241251506638307273

theorem tailTrace_2892776 : CollatzResearch.WordTrace tailWord_2892776 prefixEnd_2892776 55014241251506638307273 := by
  unfold tailWord_2892776
  simp only [CollatzResearch.WordTrace]
  refine ⟨52754104283987036826417091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70338805711982715768556121 52754104283987036826417091)
  ·
    refine ⟨79131156425980555239625637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52754104283987036826417091 79131156425980555239625637)
    ·
      refine ⟨14837091829871354107429807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79131156425980555239625637 14837091829871354107429807)
      ·
        refine ⟨22255637744807031161144711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14837091829871354107429807 22255637744807031161144711)
        ·
          refine ⟨33383456617210546741717067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22255637744807031161144711 33383456617210546741717067)
          ·
            refine ⟨50075184925815820112575601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33383456617210546741717067 50075184925815820112575601)
            ·
              refine ⟨37556388694361865084431701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50075184925815820112575601 37556388694361865084431701)
              ·
                refine ⟨55014241251506638307273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37556388694361865084431701 55014241251506638307273)
                ·
                  rfl

theorem cell23_2892776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 11].length) (baseStart_2892776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892776 prefixEnd_2892776 := by exact prefixLift 2892776
  have htrace : WordTrace (prefixWord ++ tailWord_2892776) baseStart_2892776 baseEnd_2892776 := by
    simpa [prefixWord, tailWord_2892776, baseEnd_2892776] using wordTrace_append hprefix tailTrace_2892776
  have hstable : (prefixWord ++ tailWord_2892776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892776).length < 2 ^ (prefixWord ++ tailWord_2892776).sum := by decide
  have hdescent : baseEnd_2892776 < baseStart_2892776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892783 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_2892783 : Nat := 118140960795 + 2892783 * 2 ^ 59
def prefixEnd_2892783 : Nat := 4983230072969 + 3 ^ 40 * 2892783 * 2
def baseEnd_2892783 : Nat := 1485388108155260706908839

theorem tailTrace_2892783 : CollatzResearch.WordTrace tailWord_2892783 prefixEnd_2892783 1485388108155260706908839 := by
  unfold tailWord_2892783
  simp only [CollatzResearch.WordTrace]
  refine ⟨105508463878948713848339003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70338975919299142565559335 105508463878948713848339003)
  ·
    refine ⟨158262695818423070772508505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105508463878948713848339003 158262695818423070772508505)
    ·
      refine ⟨118697021863817303079381379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158262695818423070772508505 118697021863817303079381379)
      ·
        refine ⟨178045532795725954619072069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118697021863817303079381379 178045532795725954619072069)
        ·
          refine ⟨33383537399198616491076013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178045532795725954619072069 33383537399198616491076013)
          ·
            refine ⟨12518826524699481184153505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33383537399198616491076013 12518826524699481184153505)
            ·
              refine ⟨9389119893524610888115129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12518826524699481184153505 9389119893524610888115129)
              ·
                refine ⟨7041839920143458166086347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9389119893524610888115129 7041839920143458166086347)
                ·
                  refine ⟨10562759880215187249129521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7041839920143458166086347 10562759880215187249129521)
                  ·
                    refine ⟨7922069910161390436847141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10562759880215187249129521 7922069910161390436847141)
                    ·
                      refine ⟨1485388108155260706908839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7922069910161390436847141 1485388108155260706908839)
                      ·
                        rfl

theorem cell23_2892783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_2892783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892783 prefixEnd_2892783 := by exact prefixLift 2892783
  have htrace : WordTrace (prefixWord ++ tailWord_2892783) baseStart_2892783 baseEnd_2892783 := by
    simpa [prefixWord, tailWord_2892783, baseEnd_2892783] using wordTrace_append hprefix tailTrace_2892783
  have hstable : (prefixWord ++ tailWord_2892783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892783).length < 2 ^ (prefixWord ++ tailWord_2892783).sum := by decide
  have hdescent : baseEnd_2892783 < baseStart_2892783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892788 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2892788 : Nat := 118140960795 + 2892788 * 2 ^ 59
def prefixEnd_2892788 : Nat := 4983230072969 + 3 ^ 40 * 2892788 * 2
def baseEnd_2892788 : Nat := 165043408395392576371813

theorem tailTrace_2892788 : CollatzResearch.WordTrace tailWord_2892788 prefixEnd_2892788 165043408395392576371813 := by
  unfold tailWord_2892788
  simp only [CollatzResearch.WordTrace]
  refine ⟨52754323121965299851135509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70339097495953733134847345 52754323121965299851135509)
  ·
    refine ⟨2472858896342123430521977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52754323121965299851135509 2472858896342123430521977)
    ·
      refine ⟨1854644172256592572891483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2472858896342123430521977 1854644172256592572891483)
      ·
        refine ⟨2781966258384888859337225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854644172256592572891483 2781966258384888859337225)
        ·
          refine ⟨2086474693788666644502919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781966258384888859337225 2086474693788666644502919)
          ·
            refine ⟨3129712040682999966754379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086474693788666644502919 3129712040682999966754379)
            ·
              refine ⟨4694568061024499950131569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129712040682999966754379 4694568061024499950131569)
              ·
                refine ⟨3520926045768374962598677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4694568061024499950131569 3520926045768374962598677)
                ·
                  refine ⟨165043408395392576371813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3520926045768374962598677 165043408395392576371813)
                  ·
                    rfl

theorem cell23_2892788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2892788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892788 prefixEnd_2892788 := by exact prefixLift 2892788
  have htrace : WordTrace (prefixWord ++ tailWord_2892788) baseStart_2892788 baseEnd_2892788 := by
    simpa [prefixWord, tailWord_2892788, baseEnd_2892788] using wordTrace_append hprefix tailTrace_2892788
  have hstable : (prefixWord ++ tailWord_2892788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892788).length < 2 ^ (prefixWord ++ tailWord_2892788).sum := by decide
  have hdescent : baseEnd_2892788 < baseStart_2892788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892816 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_2892816 : Nat := 118140960795 + 2892816 * 2 ^ 59
def prefixEnd_2892816 : Nat := 4983230072969 + 3 ^ 40 * 2892816 * 2
def baseEnd_2892816 : Nat := 1485405053016859077796187

theorem tailTrace_2892816 : CollatzResearch.WordTrace tailWord_2892816 prefixEnd_2892816 1485405053016859077796187 := by
  unfold tailWord_2892816
  simp only [CollatzResearch.WordTrace]
  refine ⟨52754833743914580242145151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70339778325219440322860201 52754833743914580242145151)
  ·
    refine ⟨79132250615871870363217727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52754833743914580242145151 79132250615871870363217727)
    ·
      refine ⟨118698375923807805544826591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79132250615871870363217727 118698375923807805544826591)
      ·
        refine ⟨178047563885711708317239887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118698375923807805544826591 178047563885711708317239887)
        ·
          refine ⟨267071345828567562475859831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178047563885711708317239887 267071345828567562475859831)
          ·
            refine ⟨400607018742851343713789747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267071345828567562475859831 400607018742851343713789747)
            ·
              refine ⟨600910528114277015570684621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400607018742851343713789747 600910528114277015570684621)
              ·
                refine ⟨225341448042853880839006733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 600910528114277015570684621 225341448042853880839006733)
                ·
                  refine ⟨84503043016070205314627525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225341448042853880839006733 84503043016070205314627525)
                  ·
                    refine ⟨15844320565513163496492661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84503043016070205314627525 15844320565513163496492661)
                    ·
                      refine ⟨1485405053016859077796187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15844320565513163496492661 1485405053016859077796187)
                      ·
                        rfl

theorem cell23_2892816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_2892816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892816 prefixEnd_2892816 := by exact prefixLift 2892816
  have htrace : WordTrace (prefixWord ++ tailWord_2892816) baseStart_2892816 baseEnd_2892816 := by
    simpa [prefixWord, tailWord_2892816, baseEnd_2892816] using wordTrace_append hprefix tailTrace_2892816
  have hstable : (prefixWord ++ tailWord_2892816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892816).length < 2 ^ (prefixWord ++ tailWord_2892816).sum := by decide
  have hdescent : baseEnd_2892816 < baseStart_2892816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892833 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2892833 : Nat := 118140960795 + 2892833 * 2 ^ 59
def prefixEnd_2892833 : Nat := 4983230072969 + 3 ^ 40 * 2892833 * 2
def baseEnd_2892833 : Nat := 1485413782187985511283609

theorem tailTrace_2892833 : CollatzResearch.WordTrace tailWord_2892833 prefixEnd_2892833 1485413782187985511283609 := by
  unfold tailWord_2892833
  simp only [CollatzResearch.WordTrace]
  refine ⟨105510287528767572387659153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70340191685845048258439435 105510287528767572387659153)
  ·
    refine ⟨79132715646575679290744365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105510287528767572387659153 79132715646575679290744365)
    ·
      refine ⟨29674768367465879734029137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79132715646575679290744365 29674768367465879734029137)
      ·
        refine ⟨22256076275599409800521853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29674768367465879734029137 22256076275599409800521853)
        ·
          refine ⟨8346028603349778675195695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22256076275599409800521853 8346028603349778675195695)
          ·
            refine ⟨12519042905024668012793543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346028603349778675195695 12519042905024668012793543)
            ·
              refine ⟨18778564357537002019190315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12519042905024668012793543 18778564357537002019190315)
              ·
                refine ⟨28167846536305503028785473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18778564357537002019190315 28167846536305503028785473)
                ·
                  refine ⟨21125884902229127271589105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28167846536305503028785473 21125884902229127271589105)
                  ·
                    refine ⟨15844413676671845453691829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21125884902229127271589105 15844413676671845453691829)
                    ·
                      refine ⟨1485413782187985511283609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15844413676671845453691829 1485413782187985511283609)
                      ·
                        rfl

theorem cell23_2892833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2892833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892833 prefixEnd_2892833 := by exact prefixLift 2892833
  have htrace : WordTrace (prefixWord ++ tailWord_2892833) baseStart_2892833 baseEnd_2892833 := by
    simpa [prefixWord, tailWord_2892833, baseEnd_2892833] using wordTrace_append hprefix tailTrace_2892833
  have hstable : (prefixWord ++ tailWord_2892833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892833).length < 2 ^ (prefixWord ++ tailWord_2892833).sum := by decide
  have hdescent : baseEnd_2892833 < baseStart_2892833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892863 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_2892863 : Nat := 118140960795 + 2892863 * 2 ^ 59
def prefixEnd_2892863 : Nat := 4983230072969 + 3 ^ 40 * 2892863 * 2
def baseEnd_2892863 : Nat := 1485429186607620393908471

theorem tailTrace_2892863 : CollatzResearch.WordTrace tailWord_2892863 prefixEnd_2892863 1485429186607620393908471 := by
  unfold tailWord_2892863
  simp only [CollatzResearch.WordTrace]
  refine ⟨105511381718658887511251243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70340921145772591674167495 105511381718658887511251243)
  ·
    refine ⟨158267072577988331266876865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105511381718658887511251243 158267072577988331266876865)
    ·
      refine ⟨118700304433491248450157649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158267072577988331266876865 118700304433491248450157649)
      ·
        refine ⟨89025228325118436337618237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118700304433491248450157649 89025228325118436337618237)
        ·
          refine ⟨33384460621919413626606839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89025228325118436337618237 33384460621919413626606839)
          ·
            refine ⟨50076690932879120439910259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33384460621919413626606839 50076690932879120439910259)
            ·
              refine ⟨75115036399318680659865389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50076690932879120439910259 75115036399318680659865389)
              ·
                refine ⟨28168138649744505247449521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75115036399318680659865389 28168138649744505247449521)
                ·
                  refine ⟨21126103987308378935587141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28168138649744505247449521 21126103987308378935587141)
                  ·
                    refine ⟨3961144497620321050422589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21126103987308378935587141 3961144497620321050422589)
                    ·
                      refine ⟨1485429186607620393908471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961144497620321050422589 1485429186607620393908471)
                      ·
                        rfl

theorem cell23_2892863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_2892863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892863 prefixEnd_2892863 := by exact prefixLift 2892863
  have htrace : WordTrace (prefixWord ++ tailWord_2892863) baseStart_2892863 baseEnd_2892863 := by
    simpa [prefixWord, tailWord_2892863, baseEnd_2892863] using wordTrace_append hprefix tailTrace_2892863
  have hstable : (prefixWord ++ tailWord_2892863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892863).length < 2 ^ (prefixWord ++ tailWord_2892863).sum := by decide
  have hdescent : baseEnd_2892863 < baseStart_2892863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892900 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 5]
def baseStart_2892900 : Nat := 118140960795 + 2892900 * 2 ^ 59
def prefixEnd_2892900 : Nat := 4983230072969 + 3 ^ 40 * 2892900 * 2
def baseEnd_2892900 : Nat := 165049798376870749905089

theorem tailTrace_2892900 : CollatzResearch.WordTrace tailWord_2892900 prefixEnd_2892900 165049798376870749905089 := by
  unfold tailWord_2892900
  simp only [CollatzResearch.WordTrace]
  refine ⟨52756365609762421415174077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70341820813016561886898769 52756365609762421415174077)
  ·
    refine ⟨19783637103660908030690279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52756365609762421415174077 19783637103660908030690279)
    ·
      refine ⟨29675455655491362046035419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19783637103660908030690279 29675455655491362046035419)
      ·
        refine ⟨44513183483237043069053129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29675455655491362046035419 44513183483237043069053129)
        ·
          refine ⟨33384887612427782301789847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44513183483237043069053129 33384887612427782301789847)
          ·
            refine ⟨50077331418641673452684771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33384887612427782301789847 50077331418641673452684771)
            ·
              refine ⟨75115997127962510179027157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50077331418641673452684771 75115997127962510179027157)
              ·
                refine ⟨1760531182686621332320949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75115997127962510179027157 1760531182686621332320949)
                ·
                  refine ⟨165049798376870749905089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1760531182686621332320949 165049798376870749905089)
                  ·
                    rfl

theorem cell23_2892900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_2892900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892900 prefixEnd_2892900 := by exact prefixLift 2892900
  have htrace : WordTrace (prefixWord ++ tailWord_2892900) baseStart_2892900 baseEnd_2892900 := by
    simpa [prefixWord, tailWord_2892900, baseEnd_2892900] using wordTrace_append hprefix tailTrace_2892900
  have hstable : (prefixWord ++ tailWord_2892900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892900).length < 2 ^ (prefixWord ++ tailWord_2892900).sum := by decide
  have hdescent : baseEnd_2892900 < baseStart_2892900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892913 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_2892913 : Nat := 118140960795 + 2892913 * 2 ^ 59
def prefixEnd_2892913 : Nat := 4983230072969 + 3 ^ 40 * 2892913 * 2
def baseEnd_2892913 : Nat := 495151620213448399427747

theorem tailTrace_2892913 : CollatzResearch.WordTrace tailWord_2892913 prefixEnd_2892913 495151620213448399427747 := by
  unfold tailWord_2892913
  simp only [CollatzResearch.WordTrace]
  refine ⟨105513205368477746050571393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70342136912318497367047595 105513205368477746050571393)
  ·
    refine ⟨79134904026358309537928545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105513205368477746050571393 79134904026358309537928545)
    ·
      refine ⟨59351178019768732153446409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79134904026358309537928545 59351178019768732153446409)
      ·
        refine ⟨44513383514826549115084807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59351178019768732153446409 44513383514826549115084807)
        ·
          refine ⟨66770075272239823672627211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44513383514826549115084807 66770075272239823672627211)
          ·
            refine ⟨100155112908359735508940817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66770075272239823672627211 100155112908359735508940817)
            ·
              refine ⟨75116334681269801631705613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100155112908359735508940817 75116334681269801631705613)
              ·
                refine ⟨28168625505476175611889605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75116334681269801631705613 28168625505476175611889605)
                ·
                  refine ⟨5281617282276782927229301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28168625505476175611889605 5281617282276782927229301)
                  ·
                    refine ⟨495151620213448399427747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5281617282276782927229301 495151620213448399427747)
                    ·
                      rfl

theorem cell23_2892913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_2892913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892913 prefixEnd_2892913 := by exact prefixLift 2892913
  have htrace : WordTrace (prefixWord ++ tailWord_2892913) baseStart_2892913 baseEnd_2892913 := by
    simpa [prefixWord, tailWord_2892913, baseEnd_2892913] using wordTrace_append hprefix tailTrace_2892913
  have hstable : (prefixWord ++ tailWord_2892913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892913).length < 2 ^ (prefixWord ++ tailWord_2892913).sum := by decide
  have hdescent : baseEnd_2892913 < baseStart_2892913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892920 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 2, 5, 2]
def baseStart_2892920 : Nat := 118140960795 + 2892920 * 2 ^ 59
def prefixEnd_2892920 : Nat := 4983230072969 + 3 ^ 40 * 2892920 * 2
def baseEnd_2892920 : Nat := 1485458455004926670895709

theorem tailTrace_2892920 : CollatzResearch.WordTrace tailWord_2892920 prefixEnd_2892920 1485458455004926670895709 := by
  unfold tailWord_2892920
  simp only [CollatzResearch.WordTrace]
  refine ⟨52756730339726193123038107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70342307119634924164050809 52756730339726193123038107)
  ·
    refine ⟨79135095509589289684557161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52756730339726193123038107 79135095509589289684557161)
    ·
      refine ⟨59351321632191967263417871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79135095509589289684557161 59351321632191967263417871)
      ·
        refine ⟨89026982448287950895126807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59351321632191967263417871 89026982448287950895126807)
        ·
          refine ⟨133540473672431926342690211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89026982448287950895126807 133540473672431926342690211)
          ·
            refine ⟨200310710508647889514035317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133540473672431926342690211 200310710508647889514035317)
            ·
              refine ⟨18779129110185739641940811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200310710508647889514035317 18779129110185739641940811)
              ·
                refine ⟨28168693665278609462911217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18779129110185739641940811 28168693665278609462911217)
                ·
                  refine ⟨21126520248958957097183413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28168693665278609462911217 21126520248958957097183413)
                  ·
                    refine ⟨1980611273339902227860945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21126520248958957097183413 1980611273339902227860945)
                    ·
                      refine ⟨1485458455004926670895709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980611273339902227860945 1485458455004926670895709)
                      ·
                        rfl

theorem cell23_2892920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_2892920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892920 prefixEnd_2892920 := by exact prefixLift 2892920
  have htrace : WordTrace (prefixWord ++ tailWord_2892920) baseStart_2892920 baseEnd_2892920 := by
    simpa [prefixWord, tailWord_2892920, baseEnd_2892920] using wordTrace_append hprefix tailTrace_2892920
  have hstable : (prefixWord ++ tailWord_2892920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892920).length < 2 ^ (prefixWord ++ tailWord_2892920).sum := by decide
  have hdescent : baseEnd_2892920 < baseStart_2892920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892960 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 5, 4]
def baseStart_2892960 : Nat := 118140960795 + 2892960 * 2 ^ 59
def prefixEnd_2892960 : Nat := 4983230072969 + 3 ^ 40 * 2892960 * 2
def baseEnd_2892960 : Nat := 495159664743702171465175

theorem tailTrace_2892960 : CollatzResearch.WordTrace tailWord_2892960 prefixEnd_2892960 495159664743702171465175 := by
  unfold tailWord_2892960
  simp only [CollatzResearch.WordTrace]
  refine ⟨52757459799653736538766167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70343279732871648718354889 52757459799653736538766167)
  ·
    refine ⟨79136189699480604808149251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52757459799653736538766167 79136189699480604808149251)
    ·
      refine ⟨118704284549220907212223877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79136189699480604808149251 118704284549220907212223877)
      ·
        refine ⟨22257053352978920102291977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118704284549220907212223877 22257053352978920102291977)
        ·
          refine ⟨16692790014734190076718983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22257053352978920102291977 16692790014734190076718983)
          ·
            refine ⟨25039185022101285115078475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16692790014734190076718983 25039185022101285115078475)
            ·
              refine ⟨37558777533151927672617713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25039185022101285115078475 37558777533151927672617713)
              ·
                refine ⟨28169083149863945754463285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37558777533151927672617713 28169083149863945754463285)
                ·
                  refine ⟨2640851545299744914480933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28169083149863945754463285 2640851545299744914480933)
                  ·
                    refine ⟨495159664743702171465175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640851545299744914480933 495159664743702171465175)
                    ·
                      rfl

theorem cell23_2892960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_2892960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892960 prefixEnd_2892960 := by exact prefixLift 2892960
  have htrace : WordTrace (prefixWord ++ tailWord_2892960) baseStart_2892960 baseEnd_2892960 := by
    simpa [prefixWord, tailWord_2892960, baseEnd_2892960] using wordTrace_append hprefix tailTrace_2892960
  have hstable : (prefixWord ++ tailWord_2892960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892960).length < 2 ^ (prefixWord ++ tailWord_2892960).sum := by decide
  have hdescent : baseEnd_2892960 < baseStart_2892960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892963 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4]
def baseStart_2892963 : Nat := 118140960795 + 2892963 * 2 ^ 59
def prefixEnd_2892963 : Nat := 4983230072969 + 3 ^ 40 * 2892963 * 2
def baseEnd_2892963 : Nat := 1485480534673070002658011

theorem tailTrace_2892963 : CollatzResearch.WordTrace tailWord_2892963 prefixEnd_2892963 1485480534673070002658011 := by
  unfold tailWord_2892963
  simp only [CollatzResearch.WordTrace]
  refine ⟨105515029018296604589891543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70343352678864403059927695 105515029018296604589891543)
  ·
    refine ⟨158272543527444906884837315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105515029018296604589891543 158272543527444906884837315)
    ·
      refine ⟨237408815291167360327255973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158272543527444906884837315 237408815291167360327255973)
      ·
        refine ⟨44514152867093880061360495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237408815291167360327255973 44514152867093880061360495)
        ·
          refine ⟨66771229300640820092040743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44514152867093880061360495 66771229300640820092040743)
          ·
            refine ⟨100156843950961230138061115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66771229300640820092040743 100156843950961230138061115)
            ·
              refine ⟨150235265926441845207091673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100156843950961230138061115 150235265926441845207091673)
              ·
                refine ⟨112676449444831383905318755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150235265926441845207091673 112676449444831383905318755)
                ·
                  refine ⟨169014674167247075857978133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112676449444831383905318755 169014674167247075857978133)
                  ·
                    refine ⟨7922562851589706680842725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 169014674167247075857978133 7922562851589706680842725)
                    ·
                      refine ⟨1485480534673070002658011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7922562851589706680842725 1485480534673070002658011)
                      ·
                        rfl

theorem cell23_2892963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_2892963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892963 prefixEnd_2892963 := by exact prefixLift 2892963
  have htrace : WordTrace (prefixWord ++ tailWord_2892963) baseStart_2892963 baseEnd_2892963 := by
    simpa [prefixWord, tailWord_2892963, baseEnd_2892963] using wordTrace_append hprefix tailTrace_2892963
  have hstable : (prefixWord ++ tailWord_2892963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892963).length < 2 ^ (prefixWord ++ tailWord_2892963).sum := by decide
  have hdescent : baseEnd_2892963 < baseStart_2892963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892977 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 3, 4]
def baseStart_2892977 : Nat := 118140960795 + 2892977 * 2 ^ 59
def prefixEnd_2892977 : Nat := 4983230072969 + 3 ^ 40 * 2892977 * 2
def baseEnd_2892977 : Nat := 495162574467410982627649

theorem tailTrace_2892977 : CollatzResearch.WordTrace tailWord_2892977 prefixEnd_2892977 495162574467410982627649 := by
  unfold tailWord_2892977
  simp only [CollatzResearch.WordTrace]
  refine ⟨105515539640245884980901185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70343693093497256653934123 105515539640245884980901185)
  ·
    refine ⟨79136654730184413735675889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105515539640245884980901185 79136654730184413735675889)
    ·
      refine ⟨59352491047638310301756917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79136654730184413735675889 59352491047638310301756917)
      ·
        refine ⟨5564296035716091590789711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59352491047638310301756917 5564296035716091590789711)
        ·
          refine ⟨8346444053574137386184567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564296035716091590789711 8346444053574137386184567)
          ·
            refine ⟨12519666080361206079276851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346444053574137386184567 12519666080361206079276851)
            ·
              refine ⟨18779499120541809118915277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12519666080361206079276851 18779499120541809118915277)
              ·
                refine ⟨7042312170203178419593229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18779499120541809118915277 7042312170203178419593229)
                ·
                  refine ⟨2640867063826191907347461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7042312170203178419593229 2640867063826191907347461)
                  ·
                    refine ⟨495162574467410982627649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640867063826191907347461 495162574467410982627649)
                    ·
                      rfl

theorem cell23_2892977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_2892977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892977 prefixEnd_2892977 := by exact prefixLift 2892977
  have htrace : WordTrace (prefixWord ++ tailWord_2892977) baseStart_2892977 baseEnd_2892977 := by
    simpa [prefixWord, tailWord_2892977, baseEnd_2892977] using wordTrace_append hprefix tailTrace_2892977
  have hstable : (prefixWord ++ tailWord_2892977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892977).length < 2 ^ (prefixWord ++ tailWord_2892977).sum := by decide
  have hdescent : baseEnd_2892977 < baseStart_2892977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893033 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_2893033 : Nat := 118140960795 + 2893033 * 2 ^ 59
def prefixEnd_2893033 : Nat := 4983230072969 + 3 ^ 40 * 2893033 * 2
def baseEnd_2893033 : Nat := 495172159439628242927563

theorem tailTrace_2893033 : CollatzResearch.WordTrace tailWord_2893033 prefixEnd_2893033 495172159439628242927563 := by
  unfold tailWord_2893033
  simp only [CollatzResearch.WordTrace]
  refine ⟨105517582128043006544939753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70345054752028671029959835 105517582128043006544939753)
  ·
    refine ⟨79138186596032254908704815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105517582128043006544939753 79138186596032254908704815)
    ·
      refine ⟨118707279894048382363057223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79138186596032254908704815 118707279894048382363057223)
      ·
        refine ⟨178060919841072573544585835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118707279894048382363057223 178060919841072573544585835)
        ·
          refine ⟨267091379761608860316878753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178060919841072573544585835 267091379761608860316878753)
          ·
            refine ⟨200318534821206645237659065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267091379761608860316878753 200318534821206645237659065)
            ·
              refine ⟨150238901115904983928244299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200318534821206645237659065 150238901115904983928244299)
              ·
                refine ⟨225358351673857475892366449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150238901115904983928244299 225358351673857475892366449)
                ·
                  refine ⟨169018763755393106919274837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225358351673857475892366449 169018763755393106919274837)
                  ·
                    refine ⟨495172159439628242927563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 169018763755393106919274837 495172159439628242927563)
                    ·
                      rfl

theorem cell23_2893033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_2893033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893033 prefixEnd_2893033 := by exact prefixLift 2893033
  have htrace : WordTrace (prefixWord ++ tailWord_2893033) baseStart_2893033 baseEnd_2893033 := by
    simpa [prefixWord, tailWord_2893033, baseEnd_2893033] using wordTrace_append hprefix tailTrace_2893033
  have hstable : (prefixWord ++ tailWord_2893033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893033).length < 2 ^ (prefixWord ++ tailWord_2893033).sum := by decide
  have hdescent : baseEnd_2893033 < baseStart_2893033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893034 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_2893034 : Nat := 118140960795 + 2893034 * 2 ^ 59
def prefixEnd_2893034 : Nat := 4983230072969 + 3 ^ 40 * 2893034 * 2
def baseEnd_2893034 : Nat := 1485516991799539224870185

theorem tailTrace_2893034 : CollatzResearch.WordTrace tailWord_2893034 prefixEnd_2893034 1485516991799539224870185 := by
  unfold tailWord_2893034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379404650259845928931539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70345079067359589143817437 26379404650259845928931539)
  ·
    refine ⟨39569106975389768893397309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26379404650259845928931539 39569106975389768893397309)
    ·
      refine ⟨14838415115771163335023991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39569106975389768893397309 14838415115771163335023991)
      ·
        refine ⟨22257622673656745002535987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14838415115771163335023991 22257622673656745002535987)
        ·
          refine ⟨33386434010485117503803981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22257622673656745002535987 33386434010485117503803981)
          ·
            refine ⟨12519912753931919063926493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33386434010485117503803981 12519912753931919063926493)
            ·
              refine ⟨4694967282724469648972435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12519912753931919063926493 4694967282724469648972435)
              ·
                refine ⟨7042450924086704473458653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4694967282724469648972435 7042450924086704473458653)
                ·
                  refine ⟨2640919096532514177546995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7042450924086704473458653 2640919096532514177546995)
                  ·
                    refine ⟨3961378644798771266320493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2640919096532514177546995 3961378644798771266320493)
                    ·
                      refine ⟨1485516991799539224870185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961378644798771266320493 1485516991799539224870185)
                      ·
                        rfl

theorem cell23_2893034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_2893034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893034 prefixEnd_2893034 := by exact prefixLift 2893034
  have htrace : WordTrace (prefixWord ++ tailWord_2893034) baseStart_2893034 baseEnd_2893034 := by
    simpa [prefixWord, tailWord_2893034, baseEnd_2893034] using wordTrace_append hprefix tailTrace_2893034
  have hstable : (prefixWord ++ tailWord_2893034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893034).length < 2 ^ (prefixWord ++ tailWord_2893034).sum := by decide
  have hdescent : baseEnd_2893034 < baseStart_2893034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893050 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_2893050 : Nat := 118140960795 + 2893050 * 2 ^ 59
def prefixEnd_2893050 : Nat := 4983230072969 + 3 ^ 40 * 2893050 * 2
def baseEnd_2893050 : Nat := 495175069163337054090037

theorem tailTrace_2893050 : CollatzResearch.WordTrace tailWord_2893050 prefixEnd_2893050 495175069163337054090037 := by
  unfold tailWord_2893050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379550542245354612077151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70345468112654278965539069 26379550542245354612077151)
  ·
    refine ⟨39569325813368031918115727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26379550542245354612077151 39569325813368031918115727)
    ·
      refine ⟨59353988720052047877173591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39569325813368031918115727 59353988720052047877173591)
      ·
        refine ⟨89030983080078071815760387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59353988720052047877173591 89030983080078071815760387)
        ·
          refine ⟨133546474620117107723640581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89030983080078071815760387 133546474620117107723640581)
          ·
            refine ⟨25039963991271957698182609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133546474620117107723640581 25039963991271957698182609)
            ·
              refine ⟨18779972993453968273636957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25039963991271957698182609 18779972993453968273636957)
              ·
                refine ⟨7042489872545238102613859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18779972993453968273636957 7042489872545238102613859)
                ·
                  refine ⟨10563734808817857153920789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7042489872545238102613859 10563734808817857153920789)
                  ·
                    refine ⟨495175069163337054090037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10563734808817857153920789 495175069163337054090037)
                    ·
                      rfl

theorem cell23_2893050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_2893050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893050 prefixEnd_2893050 := by exact prefixLift 2893050
  have htrace : WordTrace (prefixWord ++ tailWord_2893050) baseStart_2893050 baseEnd_2893050 := by
    simpa [prefixWord, tailWord_2893050, baseEnd_2893050] using wordTrace_append hprefix tailTrace_2893050
  have hstable : (prefixWord ++ tailWord_2893050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893050).length < 2 ^ (prefixWord ++ tailWord_2893050).sum := by decide
  have hdescent : baseEnd_2893050 < baseStart_2893050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893054 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2893054 : Nat := 118140960795 + 2893054 * 2 ^ 59
def prefixEnd_2893054 : Nat := 4983230072969 + 3 ^ 40 * 2893054 * 2
def baseEnd_2893054 : Nat := 495175753804209715540031

theorem tailTrace_2893054 : CollatzResearch.WordTrace tailWord_2893054 prefixEnd_2893054 495175753804209715540031 := by
  unfold tailWord_2893054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13189793507620865891431777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70345565373977951420969477 13189793507620865891431777)
  ·
    refine ⟨9892345130715649418573833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13189793507620865891431777 9892345130715649418573833)
    ·
      refine ⟨7419258848036737063930375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9892345130715649418573833 7419258848036737063930375)
      ·
        refine ⟨11128888272055105595895563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419258848036737063930375 11128888272055105595895563)
        ·
          refine ⟨16693332408082658393843345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11128888272055105595895563 16693332408082658393843345)
          ·
            refine ⟨12519999306061993795382509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16693332408082658393843345 12519999306061993795382509)
            ·
              refine ⟨4694999739773247673268441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12519999306061993795382509 4694999739773247673268441)
              ·
                refine ⟨3521249804829935754951331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4694999739773247673268441 3521249804829935754951331)
                ·
                  refine ⟨5281874707244903632426997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521249804829935754951331 5281874707244903632426997)
                  ·
                    refine ⟨495175753804209715540031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5281874707244903632426997 495175753804209715540031)
                    ·
                      rfl

theorem cell23_2893054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2893054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893054 prefixEnd_2893054 := by exact prefixLift 2893054
  have htrace : WordTrace (prefixWord ++ tailWord_2893054) baseStart_2893054 baseEnd_2893054 := by
    simpa [prefixWord, tailWord_2893054, baseEnd_2893054] using wordTrace_append hprefix tailTrace_2893054
  have hstable : (prefixWord ++ tailWord_2893054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893054).length < 2 ^ (prefixWord ++ tailWord_2893054).sum := by decide
  have hdescent : baseEnd_2893054 < baseStart_2893054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893057 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2893057 : Nat := 118140960795 + 2893057 * 2 ^ 59
def prefixEnd_2893057 : Nat := 4983230072969 + 3 ^ 40 * 2893057 * 2
def baseEnd_2893057 : Nat := 1485528801854592634882579

theorem tailTrace_2893057 : CollatzResearch.WordTrace tailWord_2893057 prefixEnd_2893057 1485528801854592634882579 := by
  unfold tailWord_2893057
  simp only [CollatzResearch.WordTrace]
  refine ⟨105518457479956058643813425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70345638319970705762542283 105518457479956058643813425)
  ·
    refine ⟨79138843109967043982860069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105518457479956058643813425 79138843109967043982860069)
    ·
      refine ⟨14838533083118820746786263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79138843109967043982860069 14838533083118820746786263)
      ·
        refine ⟨22257799624678231120179395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14838533083118820746786263 22257799624678231120179395)
        ·
          refine ⟨33386699437017346680269093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22257799624678231120179395 33386699437017346680269093)
          ·
            refine ⟨6260006144440752502550455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33386699437017346680269093 6260006144440752502550455)
            ·
              refine ⟨9390009216661128753825683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260006144440752502550455 9390009216661128753825683)
              ·
                refine ⟨14085013824991693130738525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9390009216661128753825683 14085013824991693130738525)
                ·
                  refine ⟨5281880184371884924026947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14085013824991693130738525 5281880184371884924026947)
                  ·
                    refine ⟨7922820276557827386040421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5281880184371884924026947 7922820276557827386040421)
                    ·
                      refine ⟨1485528801854592634882579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7922820276557827386040421 1485528801854592634882579)
                      ·
                        rfl

theorem cell23_2893057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2893057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893057 prefixEnd_2893057 := by exact prefixLift 2893057
  have htrace : WordTrace (prefixWord ++ tailWord_2893057) baseStart_2893057 baseEnd_2893057 := by
    simpa [prefixWord, tailWord_2893057, baseEnd_2893057] using wordTrace_append hprefix tailTrace_2893057
  have hstable : (prefixWord ++ tailWord_2893057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893057).length < 2 ^ (prefixWord ++ tailWord_2893057).sum := by decide
  have hdescent : baseEnd_2893057 < baseStart_2893057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893085 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_2893085 : Nat := 118140960795 + 2893085 * 2 ^ 59
def prefixEnd_2893085 : Nat := 4983230072969 + 3 ^ 40 * 2893085 * 2
def baseEnd_2893085 : Nat := 1485543179312918525332451

theorem tailTrace_2893085 : CollatzResearch.WordTrace tailWord_2893085 prefixEnd_2893085 1485543179312918525332451 := by
  unfold tailWord_2893085
  simp only [CollatzResearch.WordTrace]
  refine ⟨105519478723854619425832709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70346319149236412950555139 105519478723854619425832709)
  ·
    refine ⟨19784902260722741142343633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105519478723854619425832709 19784902260722741142343633)
    ·
      refine ⟨14838676695542055856757725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19784902260722741142343633 14838676695542055856757725)
      ·
        refine ⟨5564503760828270946284147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14838676695542055856757725 5564503760828270946284147)
        ·
          refine ⟨8346755641242406419426221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564503760828270946284147 8346755641242406419426221)
          ·
            refine ⟨3130033365465902407284833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8346755641242406419426221 3130033365465902407284833)
            ·
              refine ⟨2347525024099426805463625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130033365465902407284833 2347525024099426805463625)
              ·
                refine ⟨1760643768074570104097719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347525024099426805463625 1760643768074570104097719)
                ·
                  refine ⟨2640965652111855156146579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760643768074570104097719 2640965652111855156146579)
                  ·
                    refine ⟨3961448478167782734219869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2640965652111855156146579 3961448478167782734219869)
                    ·
                      refine ⟨1485543179312918525332451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961448478167782734219869 1485543179312918525332451)
                      ·
                        rfl

theorem cell23_2893085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_2893085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893085 prefixEnd_2893085 := by exact prefixLift 2893085
  have htrace : WordTrace (prefixWord ++ tailWord_2893085) baseStart_2893085 baseEnd_2893085 := by
    simpa [prefixWord, tailWord_2893085, baseEnd_2893085] using wordTrace_append hprefix tailTrace_2893085
  have hstable : (prefixWord ++ tailWord_2893085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893085).length < 2 ^ (prefixWord ++ tailWord_2893085).sum := by decide
  have hdescent : baseEnd_2893085 < baseStart_2893085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893101 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2893101 : Nat := 118140960795 + 2893101 * 2 ^ 59
def prefixEnd_2893101 : Nat := 4983230072969 + 3 ^ 40 * 2893101 * 2
def baseEnd_2893101 : Nat := 495183798334463487577459

theorem tailTrace_2893101 : CollatzResearch.WordTrace tailWord_2893101 prefixEnd_2893101 495183798334463487577459 := by
  unfold tailWord_2893101
  simp only [CollatzResearch.WordTrace]
  refine ⟨105520062291796654158415157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70346708194531102772276771 105520062291796654158415157)
  ·
    refine ⟨9892505839855936327351421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105520062291796654158415157 9892505839855936327351421)
    ·
      refine ⟨3709689689945976122756783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9892505839855936327351421 3709689689945976122756783)
      ·
        refine ⟨5564534534918964184135175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709689689945976122756783 5564534534918964184135175)
        ·
          refine ⟨8346801802378446276202763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564534534918964184135175 8346801802378446276202763)
          ·
            refine ⟨12520202703567669414304145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346801802378446276202763 12520202703567669414304145)
            ·
              refine ⟨9390152027675752060728109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12520202703567669414304145 9390152027675752060728109)
              ·
                refine ⟨3521307010378407022773041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9390152027675752060728109 3521307010378407022773041)
                ·
                  refine ⟨2640980257783805267079781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521307010378407022773041 2640980257783805267079781)
                  ·
                    refine ⟨495183798334463487577459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2640980257783805267079781 495183798334463487577459)
                    ·
                      rfl

theorem cell23_2893101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2893101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893101 prefixEnd_2893101 := by exact prefixLift 2893101
  have htrace : WordTrace (prefixWord ++ tailWord_2893101) baseStart_2893101 baseEnd_2893101 := by
    simpa [prefixWord, tailWord_2893101, baseEnd_2893101] using wordTrace_append hprefix tailTrace_2893101
  have hstable : (prefixWord ++ tailWord_2893101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893101).length < 2 ^ (prefixWord ++ tailWord_2893101).sum := by decide
  have hdescent : baseEnd_2893101 < baseStart_2893101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893107 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 3]
def baseStart_2893107 : Nat := 118140960795 + 2893107 * 2 ^ 59
def prefixEnd_2893107 : Nat := 4983230072969 + 3 ^ 40 * 2893107 * 2
def baseEnd_2893107 : Nat := 1485554475887317439257349

theorem tailTrace_2893107 : CollatzResearch.WordTrace tailWord_2893107 prefixEnd_2893107 1485554475887317439257349 := by
  unfold tailWord_2893107
  simp only [CollatzResearch.WordTrace]
  refine ⟨105520281129774917183133575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70346854086516611455422383 105520281129774917183133575)
  ·
    refine ⟨158280421694662375774700363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105520281129774917183133575 158280421694662375774700363)
    ·
      refine ⟨237420632541993563662050545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158280421694662375774700363 237420632541993563662050545)
      ·
        refine ⟨178065474406495172746537909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237420632541993563662050545 178065474406495172746537909)
        ·
          refine ⟨16693638225608922444987929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178065474406495172746537909 16693638225608922444987929)
          ·
            refine ⟨12520228669206691833740947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16693638225608922444987929 12520228669206691833740947)
            ·
              refine ⟨18780343003810037750611421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12520228669206691833740947 18780343003810037750611421)
              ·
                refine ⟨7042628626428764156479283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18780343003810037750611421 7042628626428764156479283)
                ·
                  refine ⟨10563942939643146234718925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7042628626428764156479283 10563942939643146234718925)
                  ·
                    refine ⟨3961478602366179838019597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10563942939643146234718925 3961478602366179838019597)
                    ·
                      refine ⟨1485554475887317439257349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961478602366179838019597 1485554475887317439257349)
                      ·
                        rfl

theorem cell23_2893107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_2893107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893107 prefixEnd_2893107 := by exact prefixLift 2893107
  have htrace : WordTrace (prefixWord ++ tailWord_2893107) baseStart_2893107 baseEnd_2893107 := by
    simpa [prefixWord, tailWord_2893107, baseEnd_2893107] using wordTrace_append hprefix tailTrace_2893107
  have hstable : (prefixWord ++ tailWord_2893107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893107).length < 2 ^ (prefixWord ++ tailWord_2893107).sum := by decide
  have hdescent : baseEnd_2893107 < baseStart_2893107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893120 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_2893120 : Nat := 118140960795 + 2893120 * 2 ^ 59
def prefixEnd_2893120 : Nat := 4983230072969 + 3 ^ 40 * 2893120 * 2
def baseEnd_2893120 : Nat := 1485561151135825888394789

theorem tailTrace_2893120 : CollatzResearch.WordTrace tailWord_2893120 prefixEnd_2893120 1485561151135825888394789 := by
  unfold tailWord_2893120
  simp only [CollatzResearch.WordTrace]
  refine ⟨52760377639363910201678407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70347170185818546935571209 52760377639363910201678407)
  ·
    refine ⟨79140566459045865302517611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52760377639363910201678407 79140566459045865302517611)
    ·
      refine ⟨118710849688568797953776417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79140566459045865302517611 118710849688568797953776417)
      ·
        refine ⟨89033137266426598465332313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118710849688568797953776417 89033137266426598465332313)
        ·
          refine ⟨66774852949819948848999235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89033137266426598465332313 66774852949819948848999235)
          ·
            refine ⟨100162279424729923273498853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66774852949819948848999235 100162279424729923273498853)
            ·
              refine ⟨18780427392136860613781035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100162279424729923273498853 18780427392136860613781035)
              ·
                refine ⟨28170641088205290920671553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18780427392136860613781035 28170641088205290920671553)
                ·
                  refine ⟨21127980816153968190503665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28170641088205290920671553 21127980816153968190503665)
                  ·
                    refine ⟨15845985612115476142877749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21127980816153968190503665 15845985612115476142877749)
                    ·
                      refine ⟨1485561151135825888394789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15845985612115476142877749 1485561151135825888394789)
                      ·
                        rfl

theorem cell23_2893120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_2893120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893120 prefixEnd_2893120 := by exact prefixLift 2893120
  have htrace : WordTrace (prefixWord ++ tailWord_2893120) baseStart_2893120 baseEnd_2893120 := by
    simpa [prefixWord, tailWord_2893120, baseEnd_2893120] using wordTrace_append hprefix tailTrace_2893120
  have hstable : (prefixWord ++ tailWord_2893120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893120).length < 2 ^ (prefixWord ++ tailWord_2893120).sum := by decide
  have hdescent : baseEnd_2893120 < baseStart_2893120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893141 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2893141 : Nat := 118140960795 + 2893141 * 2 ^ 59
def prefixEnd_2893141 : Nat := 4983230072969 + 3 ^ 40 * 2893141 * 2
def baseEnd_2893141 : Nat := 1485571934229570306232193

theorem tailTrace_2893141 : CollatzResearch.WordTrace tailWord_2893141 prefixEnd_2893141 1485571934229570306232193 := by
  unfold tailWord_2893141
  simp only [CollatzResearch.WordTrace]
  refine ⟨105521521211651740989871277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70347680807767827326580851 105521521211651740989871277)
  ·
    refine ⟨39570570454369402871201729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105521521211651740989871277 39570570454369402871201729)
    ·
      refine ⟨29677927840777052153401297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39570570454369402871201729 29677927840777052153401297)
      ·
        refine ⟨22258445880582789115050973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29677927840777052153401297 22258445880582789115050973)
        ·
          refine ⟨8346917205218545918144115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22258445880582789115050973 8346917205218545918144115)
          ·
            refine ⟨12520375807827818877216173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346917205218545918144115 12520375807827818877216173)
            ·
              refine ⟨4695140927935432078956065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12520375807827818877216173 4695140927935432078956065)
              ·
                refine ⟨3521355695951574059217049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4695140927935432078956065 3521355695951574059217049)
                ·
                  refine ⟨2641016771963680544412787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521355695951574059217049 2641016771963680544412787)
                  ·
                    refine ⟨3961525157945520816619181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641016771963680544412787 3961525157945520816619181)
                    ·
                      refine ⟨1485571934229570306232193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961525157945520816619181 1485571934229570306232193)
                      ·
                        rfl

theorem cell23_2893141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2893141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893141 prefixEnd_2893141 := by exact prefixLift 2893141
  have htrace : WordTrace (prefixWord ++ tailWord_2893141) baseStart_2893141 baseEnd_2893141 := by
    simpa [prefixWord, tailWord_2893141, baseEnd_2893141] using wordTrace_append hprefix tailTrace_2893141
  have hstable : (prefixWord ++ tailWord_2893141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893141).length < 2 ^ (prefixWord ++ tailWord_2893141).sum := by decide
  have hdescent : baseEnd_2893141 < baseStart_2893141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893204 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 7]
def baseStart_2893204 : Nat := 118140960795 + 2893204 * 2 ^ 59
def prefixEnd_2893204 : Nat := 4983230072969 + 3 ^ 40 * 2893204 * 2
def baseEnd_2893204 : Nat := 165067142612311506638267

theorem tailTrace_2893204 : CollatzResearch.WordTrace tailWord_2893204 prefixEnd_2893204 165067142612311506638267 := by
  unfold tailWord_2893204
  simp only [CollatzResearch.WordTrace]
  refine ⟨52761909505211751374707333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70349212673615668499609777 52761909505211751374707333)
  ·
    refine ⟨9892858032227203382757625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52761909505211751374707333 9892858032227203382757625)
    ·
      refine ⟨7419643524170402537068219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9892858032227203382757625 7419643524170402537068219)
      ·
        refine ⟨11129465286255603805602329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419643524170402537068219 11129465286255603805602329)
        ·
          refine ⟨8347098964691702854201747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11129465286255603805602329 8347098964691702854201747)
          ·
            refine ⟨12520648447037554281302621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347098964691702854201747 12520648447037554281302621)
            ·
              refine ⟨4695243167639082855488483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12520648447037554281302621 4695243167639082855488483)
              ·
                refine ⟨7042864751458624283232725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695243167639082855488483 7042864751458624283232725)
                ·
                  refine ⟨165067142612311506638267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7042864751458624283232725 165067142612311506638267)
                  ·
                    rfl

theorem cell23_2893204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_2893204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893204 prefixEnd_2893204 := by exact prefixLift 2893204
  have htrace : WordTrace (prefixWord ++ tailWord_2893204) baseStart_2893204 baseEnd_2893204 := by
    simpa [prefixWord, tailWord_2893204, baseEnd_2893204] using wordTrace_append hprefix tailTrace_2893204
  have hstable : (prefixWord ++ tailWord_2893204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893204).length < 2 ^ (prefixWord ++ tailWord_2893204).sum := by decide
  have hdescent : baseEnd_2893204 < baseStart_2893204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893215 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 2, 2, 2]
def baseStart_2893215 : Nat := 118140960795 + 2893215 * 2 ^ 59
def prefixEnd_2893215 : Nat := 4983230072969 + 3 ^ 40 * 2893215 * 2
def baseEnd_2893215 : Nat := 1485609931798003016706853

theorem tailTrace_2893215 : CollatzResearch.WordTrace tailWord_2893215 prefixEnd_2893215 1485609931798003016706853 := by
  unfold tailWord_2893215
  simp only [CollatzResearch.WordTrace]
  refine ⟨105524220213383651628065099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70349480142255767752043399 105524220213383651628065099)
  ·
    refine ⟨158286330320075477442097649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105524220213383651628065099 158286330320075477442097649)
    ·
      refine ⟨118714747740056608081573237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158286330320075477442097649 118714747740056608081573237)
      ·
        refine ⟨11129507600630307007647491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118714747740056608081573237 11129507600630307007647491)
        ·
          refine ⟨16694261400945460511471237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11129507600630307007647491 16694261400945460511471237)
          ·
            refine ⟨3130174012677273845900857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16694261400945460511471237 3130174012677273845900857)
            ·
              refine ⟨2347630509507955384425643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130174012677273845900857 2347630509507955384425643)
              ·
                refine ⟨3521445764261933076638465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347630509507955384425643 3521445764261933076638465)
                ·
                  refine ⟨2641084323196449807478849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521445764261933076638465 2641084323196449807478849)
                  ·
                    refine ⟨1980813242397337355609137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641084323196449807478849 1980813242397337355609137)
                    ·
                      refine ⟨1485609931798003016706853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980813242397337355609137 1485609931798003016706853)
                      ·
                        rfl

theorem cell23_2893215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_2893215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893215 prefixEnd_2893215 := by exact prefixLift 2893215
  have htrace : WordTrace (prefixWord ++ tailWord_2893215) baseStart_2893215 baseEnd_2893215 := by
    simpa [prefixWord, tailWord_2893215, baseEnd_2893215] using wordTrace_append hprefix tailTrace_2893215
  have hstable : (prefixWord ++ tailWord_2893215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893215).length < 2 ^ (prefixWord ++ tailWord_2893215).sum := by decide
  have hdescent : baseEnd_2893215 < baseStart_2893215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893257 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_2893257 : Nat := 118140960795 + 2893257 * 2 ^ 59
def prefixEnd_2893257 : Nat := 4983230072969 + 3 ^ 40 * 2893257 * 2
def baseEnd_2893257 : Nat := 1485631497985491852381659

theorem tailTrace_2893257 : CollatzResearch.WordTrace tailWord_2893257 prefixEnd_2893257 1485631497985491852381659 := by
  unfold tailWord_2893257
  simp only [CollatzResearch.WordTrace]
  refine ⟨105525752079231492801094025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70350501386154328534062683 105525752079231492801094025)
  ·
    refine ⟨79144314059423619600820519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105525752079231492801094025 79144314059423619600820519)
    ·
      refine ⟨118716471089135429401230779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79144314059423619600820519 118716471089135429401230779)
      ·
        refine ⟨178074706633703144101846169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118716471089135429401230779 178074706633703144101846169)
        ·
          refine ⟨133556029975277358076384627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178074706633703144101846169 133556029975277358076384627)
          ·
            refine ⟨200334044962916037114576941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133556029975277358076384627 200334044962916037114576941)
            ·
              refine ⟨75125266861093513917966353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200334044962916037114576941 75125266861093513917966353)
              ·
                refine ⟨56343950145820135438474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75125266861093513917966353 56343950145820135438474765)
                ·
                  refine ⟨21128981304682550789428037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56343950145820135438474765 21128981304682550789428037)
                  ·
                    refine ⟨3961683994627978273017757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21128981304682550789428037 3961683994627978273017757)
                    ·
                      refine ⟨1485631497985491852381659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961683994627978273017757 1485631497985491852381659)
                      ·
                        rfl

theorem cell23_2893257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_2893257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893257 prefixEnd_2893257 := by exact prefixLift 2893257
  have htrace : WordTrace (prefixWord ++ tailWord_2893257) baseStart_2893257 baseEnd_2893257 := by
    simpa [prefixWord, tailWord_2893257, baseEnd_2893257] using wordTrace_append hprefix tailTrace_2893257
  have hstable : (prefixWord ++ tailWord_2893257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893257).length < 2 ^ (prefixWord ++ tailWord_2893257).sum := by decide
  have hdescent : baseEnd_2893257 < baseStart_2893257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893298 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_2893298 : Nat := 118140960795 + 2893298 * 2 ^ 59
def prefixEnd_2893298 : Nat := 4983230072969 + 3 ^ 40 * 2893298 * 2
def baseEnd_2893298 : Nat := 495217516897442063989657

theorem tailTrace_2893298 : CollatzResearch.WordTrace tailWord_2893298 prefixEnd_2893298 495217516897442063989657 := by
  unfold tailWord_2893298
  simp only [CollatzResearch.WordTrace]
  refine ⟨26381811868020739200834137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70351498314721971202224365 26381811868020739200834137)
  ·
    refine ⟨19786358901015554400625603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26381811868020739200834137 19786358901015554400625603)
    ·
      refine ⟨29679538351523331600938405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19786358901015554400625603 29679538351523331600938405)
      ·
        refine ⟨5564913440910624675175951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29679538351523331600938405 5564913440910624675175951)
        ·
          refine ⟨8347370161365937012763927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564913440910624675175951 8347370161365937012763927)
          ·
            refine ⟨12521055242048905519145891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347370161365937012763927 12521055242048905519145891)
            ·
              refine ⟨18781582863073358278718837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12521055242048905519145891 18781582863073358278718837)
              ·
                refine ⟨1760773393413127338629891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18781582863073358278718837 1760773393413127338629891)
                ·
                  refine ⟨2641160090119691007944837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760773393413127338629891 2641160090119691007944837)
                  ·
                    refine ⟨495217516897442063989657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641160090119691007944837 495217516897442063989657)
                    ·
                      rfl

theorem cell23_2893298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_2893298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893298 prefixEnd_2893298 := by exact prefixLift 2893298
  have htrace : WordTrace (prefixWord ++ tailWord_2893298) baseStart_2893298 baseEnd_2893298 := by
    simpa [prefixWord, tailWord_2893298, baseEnd_2893298] using wordTrace_append hprefix tailTrace_2893298
  have hstable : (prefixWord ++ tailWord_2893298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893298).length < 2 ^ (prefixWord ++ tailWord_2893298).sum := by decide
  have hdescent : baseEnd_2893298 < baseStart_2893298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893321 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 3]
def baseStart_2893321 : Nat := 118140960795 + 2893321 * 2 ^ 59
def prefixEnd_2893321 : Nat := 4983230072969 + 3 ^ 40 * 2893321 * 2
def baseEnd_2893321 : Nat := 1485664360747379601981365

theorem tailTrace_2893321 : CollatzResearch.WordTrace tailWord_2893321 prefixEnd_2893321 1485664360747379601981365 := by
  unfold tailWord_2893321
  simp only [CollatzResearch.WordTrace]
  refine ⟨105528086350999631731423817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70352057567333087820949211 105528086350999631731423817)
  ·
    refine ⟨79146064763249723798567863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105528086350999631731423817 79146064763249723798567863)
    ·
      refine ⟨118719097144874585697851795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79146064763249723798567863 118719097144874585697851795)
      ·
        refine ⟨178078645717311878546777693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118719097144874585697851795 178078645717311878546777693)
        ·
          refine ⟨66779492143991954455041635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178078645717311878546777693 66779492143991954455041635)
          ·
            refine ⟨100169238215987931682562453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66779492143991954455041635 100169238215987931682562453)
            ·
              refine ⟨4695433041374434297620115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100169238215987931682562453 4695433041374434297620115)
              ·
                refine ⟨7043149562061651446430173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695433041374434297620115 7043149562061651446430173)
                ·
                  refine ⟨2641181085773119292411315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7043149562061651446430173 2641181085773119292411315)
                  ·
                    refine ⟨3961771628659678938616973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641181085773119292411315 3961771628659678938616973)
                    ·
                      refine ⟨1485664360747379601981365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961771628659678938616973 1485664360747379601981365)
                      ·
                        rfl

theorem cell23_2893321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_2893321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893321 prefixEnd_2893321 := by exact prefixLift 2893321
  have htrace : WordTrace (prefixWord ++ tailWord_2893321) baseStart_2893321 baseEnd_2893321 := by
    simpa [prefixWord, tailWord_2893321, baseEnd_2893321] using wordTrace_append hprefix tailTrace_2893321
  have hstable : (prefixWord ++ tailWord_2893321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893321).length < 2 ^ (prefixWord ++ tailWord_2893321).sum := by decide
  have hdescent : baseEnd_2893321 < baseStart_2893321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893341 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2893341 : Nat := 118140960795 + 2893341 * 2 ^ 59
def prefixEnd_2893341 : Nat := 4983230072969 + 3 ^ 40 * 2893341 * 2
def baseEnd_2893341 : Nat := 495224876786823174577091

theorem tailTrace_2893341 : CollatzResearch.WordTrace tailWord_2893341 prefixEnd_2893341 495224876786823174577091 := by
  unfold tailWord_2893341
  simp only [CollatzResearch.WordTrace]
  refine ⟨105528815810927175147151877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70352543873951450098101251 105528815810927175147151877)
  ·
    refine ⟨19786652964548845340090977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105528815810927175147151877 19786652964548845340090977)
    ·
      refine ⟨14839989723411634005068233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19786652964548845340090977 14839989723411634005068233)
      ·
        refine ⟨11129992292558725503801175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14839989723411634005068233 11129992292558725503801175)
        ·
          refine ⟨16694988438838088255701763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11129992292558725503801175 16694988438838088255701763)
          ·
            refine ⟨25042482658257132383552645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16694988438838088255701763 25042482658257132383552645)
            ·
              refine ⟨4695465498423212321916121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25042482658257132383552645 4695465498423212321916121)
              ·
                refine ⟨3521599123817409241437091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4695465498423212321916121 3521599123817409241437091)
                ·
                  refine ⟨5282398685726113862155637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521599123817409241437091 5282398685726113862155637)
                  ·
                    refine ⟨495224876786823174577091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5282398685726113862155637 495224876786823174577091)
                    ·
                      rfl

theorem cell23_2893341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2893341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893341 prefixEnd_2893341 := by exact prefixLift 2893341
  have htrace : WordTrace (prefixWord ++ tailWord_2893341) baseStart_2893341 baseEnd_2893341 := by
    simpa [prefixWord, tailWord_2893341, baseEnd_2893341] using wordTrace_append hprefix tailTrace_2893341
  have hstable : (prefixWord ++ tailWord_2893341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893341).length < 2 ^ (prefixWord ++ tailWord_2893341).sum := by decide
  have hdescent : baseEnd_2893341 < baseStart_2893341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893354 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2893354 : Nat := 118140960795 + 2893354 * 2 ^ 59
def prefixEnd_2893354 : Nat := 4983230072969 + 3 ^ 40 * 2893354 * 2
def baseEnd_2893354 : Nat := 495227101869659324289571

theorem tailTrace_2893354 : CollatzResearch.WordTrace tailWord_2893354 prefixEnd_2893354 495227101869659324289571 := by
  unfold tailWord_2893354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26382322489970019591843779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70352859973253385578250077 26382322489970019591843779)
  ·
    refine ⟨39573483734955029387765669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26382322489970019591843779 39573483734955029387765669)
    ·
      refine ⟨7420028200304068010206063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39573483734955029387765669 7420028200304068010206063)
      ·
        refine ⟨11130042300456102015309095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7420028200304068010206063 11130042300456102015309095)
        ·
          refine ⟨16695063450684153022963643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11130042300456102015309095 16695063450684153022963643)
          ·
            refine ⟨25042595176026229534445465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16695063450684153022963643 25042595176026229534445465)
            ·
              refine ⟨18781946382019672150834099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25042595176026229534445465 18781946382019672150834099)
              ·
                refine ⟨28172919573029508226251149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18781946382019672150834099 28172919573029508226251149)
                ·
                  refine ⟨10564844839886065584844181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28172919573029508226251149 10564844839886065584844181)
                  ·
                    refine ⟨495227101869659324289571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10564844839886065584844181 495227101869659324289571)
                    ·
                      rfl

theorem cell23_2893354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2893354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893354 prefixEnd_2893354 := by exact prefixLift 2893354
  have htrace : WordTrace (prefixWord ++ tailWord_2893354) baseStart_2893354 baseEnd_2893354 := by
    simpa [prefixWord, tailWord_2893354, baseEnd_2893354] using wordTrace_append hprefix tailTrace_2893354
  have hstable : (prefixWord ++ tailWord_2893354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893354).length < 2 ^ (prefixWord ++ tailWord_2893354).sum := by decide
  have hdescent : baseEnd_2893354 < baseStart_2893354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893367 : List Nat := [1, 1, 3, 1, 2, 4, 11]
def baseStart_2893367 : Nat := 118140960795 + 2893367 * 2 ^ 59
def prefixEnd_2893367 : Nat := 4983230072969 + 3 ^ 40 * 2893367 * 2
def baseEnd_2893367 : Nat := 18341826924166499037113

theorem tailTrace_2893367 : CollatzResearch.WordTrace tailWord_2893367 prefixEnd_2893367 18341826924166499037113 := by
  unfold tailWord_2893367
  simp only [CollatzResearch.WordTrace]
  refine ⟨105529764108832981587598355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70353176072555321058398903 105529764108832981587598355)
  ·
    refine ⟨158294646163249472381397533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105529764108832981587598355 158294646163249472381397533)
    ·
      refine ⟨59360492311218552143024075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158294646163249472381397533 59360492311218552143024075)
      ·
        refine ⟨89040738466827828214536113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59360492311218552143024075 89040738466827828214536113)
        ·
          refine ⟨66780553850120871160902085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89040738466827828214536113 66780553850120871160902085)
          ·
            refine ⟨12521353846897663342669141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66780553850120871160902085 12521353846897663342669141)
            ·
              refine ⟨18341826924166499037113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12521353846897663342669141 18341826924166499037113)
              ·
                rfl

theorem cell23_2893367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 11].length) (baseStart_2893367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893367 prefixEnd_2893367 := by exact prefixLift 2893367
  have htrace : WordTrace (prefixWord ++ tailWord_2893367) baseStart_2893367 baseEnd_2893367 := by
    simpa [prefixWord, tailWord_2893367, baseEnd_2893367] using wordTrace_append hprefix tailTrace_2893367
  have hstable : (prefixWord ++ tailWord_2893367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893367).length < 2 ^ (prefixWord ++ tailWord_2893367).sum := by decide
  have hdescent : baseEnd_2893367 < baseStart_2893367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893372 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_2893372 : Nat := 118140960795 + 2893372 * 2 ^ 59
def prefixEnd_2893372 : Nat := 4983230072969 + 3 ^ 40 * 2893372 * 2
def baseEnd_2893372 : Nat := 1485690548260758902443631

theorem tailTrace_2893372 : CollatzResearch.WordTrace tailWord_2893372 prefixEnd_2893372 1485690548260758902443631 := by
  unfold tailWord_2893372
  simp only [CollatzResearch.WordTrace]
  refine ⟨52764973236907433720765185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70353297649209911627686913 52764973236907433720765185)
  ·
    refine ⟨39573729927680575290573889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52764973236907433720765185 39573729927680575290573889)
    ·
      refine ⟨29680297445760431467930417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39573729927680575290573889 29680297445760431467930417)
      ·
        refine ⟨22260223084320323600947813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29680297445760431467930417 22260223084320323600947813)
        ·
          refine ⟨4173791828310060675177715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22260223084320323600947813 4173791828310060675177715)
          ·
            refine ⟨6260687742465091012766573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173791828310060675177715 6260687742465091012766573)
            ·
              refine ⟨2347757903424409129787465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6260687742465091012766573 2347757903424409129787465)
              ·
                refine ⟨1760818427568306847340599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347757903424409129787465 1760818427568306847340599)
                ·
                  refine ⟨2641227641352460271010899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760818427568306847340599 2641227641352460271010899)
                  ·
                    refine ⟨3961841462028690406516349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641227641352460271010899 3961841462028690406516349)
                    ·
                      refine ⟨1485690548260758902443631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961841462028690406516349 1485690548260758902443631)
                      ·
                        rfl

theorem cell23_2893372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_2893372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893372 prefixEnd_2893372 := by exact prefixLift 2893372
  have htrace : WordTrace (prefixWord ++ tailWord_2893372) baseStart_2893372 baseEnd_2893372 := by
    simpa [prefixWord, tailWord_2893372, baseEnd_2893372] using wordTrace_append hprefix tailTrace_2893372
  have hstable : (prefixWord ++ tailWord_2893372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893372).length < 2 ^ (prefixWord ++ tailWord_2893372).sum := by decide
  have hdescent : baseEnd_2893372 < baseStart_2893372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893387 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_2893387 : Nat := 118140960795 + 2893387 * 2 ^ 59
def prefixEnd_2893387 : Nat := 4983230072969 + 3 ^ 40 * 2893387 * 2
def baseEnd_2893387 : Nat := 1485698250470576343756061

theorem tailTrace_2893387 : CollatzResearch.WordTrace tailWord_2893387 prefixEnd_2893387 1485698250470576343756061 := by
  unfold tailWord_2893387
  simp only [CollatzResearch.WordTrace]
  refine ⟨105530493568760525003326415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70353662379173683335550943 105530493568760525003326415)
  ·
    refine ⟨158295740353140787504989623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105530493568760525003326415 158295740353140787504989623)
    ·
      refine ⟨237443610529711181257484435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158295740353140787504989623 237443610529711181257484435)
      ·
        refine ⟨356165415794566771886226653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237443610529711181257484435 356165415794566771886226653)
        ·
          refine ⟨133562030922962539457334995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 356165415794566771886226653 133562030922962539457334995)
          ·
            refine ⟨200343046384443809186002493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133562030922962539457334995 200343046384443809186002493)
            ·
              refine ⟨75128642394166428444750935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200343046384443809186002493 75128642394166428444750935)
              ·
                refine ⟨112692963591249642667126403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75128642394166428444750935 112692963591249642667126403)
                ·
                  refine ⟨169039445386874464000689605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112692963591249642667126403 169039445386874464000689605)
                  ·
                    refine ⟨31694896010038962000129301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169039445386874464000689605 31694896010038962000129301)
                    ·
                      refine ⟨1485698250470576343756061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31694896010038962000129301 1485698250470576343756061)
                      ·
                        rfl

theorem cell23_2893387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_2893387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893387 prefixEnd_2893387 := by exact prefixLift 2893387
  have htrace : WordTrace (prefixWord ++ tailWord_2893387) baseStart_2893387 baseEnd_2893387 := by
    simpa [prefixWord, tailWord_2893387, baseEnd_2893387] using wordTrace_append hprefix tailTrace_2893387
  have hstable : (prefixWord ++ tailWord_2893387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893387).length < 2 ^ (prefixWord ++ tailWord_2893387).sum := by decide
  have hdescent : baseEnd_2893387 < baseStart_2893387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893388 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_2893388 : Nat := 118140960795 + 2893388 * 2 ^ 59
def prefixEnd_2893388 : Nat := 4983230072969 + 3 ^ 40 * 2893388 * 2
def baseEnd_2893388 : Nat := 495232921317076946614519

theorem tailTrace_2893388 : CollatzResearch.WordTrace tailWord_2893388 prefixEnd_2893388 495232921317076946614519 := by
  unfold tailWord_2893388
  simp only [CollatzResearch.WordTrace]
  refine ⟨52765265020878451087056409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70353686694504601449408545 52765265020878451087056409)
  ·
    refine ⟨39573948765658838315292307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52765265020878451087056409 39573948765658838315292307)
    ·
      refine ⟨59360923148488257472938461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39573948765658838315292307 59360923148488257472938461)
      ·
        refine ⟨22260346180683096552351923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59360923148488257472938461 22260346180683096552351923)
        ·
          refine ⟨33390519271024644828527885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22260346180683096552351923 33390519271024644828527885)
          ·
            refine ⟨12521444726634241810697957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33390519271024644828527885 12521444726634241810697957)
            ·
              refine ⟨2347770886243920339505867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12521444726634241810697957 2347770886243920339505867)
              ·
                refine ⟨3521656329365880509258801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347770886243920339505867 3521656329365880509258801)
                ·
                  refine ⟨2641242247024410381944101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3521656329365880509258801 2641242247024410381944101)
                  ·
                    refine ⟨495232921317076946614519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641242247024410381944101 495232921317076946614519)
                    ·
                      rfl

theorem cell23_2893388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_2893388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893388 prefixEnd_2893388 := by exact prefixLift 2893388
  have htrace : WordTrace (prefixWord ++ tailWord_2893388) baseStart_2893388 baseEnd_2893388 := by
    simpa [prefixWord, tailWord_2893388, baseEnd_2893388] using wordTrace_append hprefix tailTrace_2893388
  have hstable : (prefixWord ++ tailWord_2893388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893388).length < 2 ^ (prefixWord ++ tailWord_2893388).sum := by decide
  have hdescent : baseEnd_2893388 < baseStart_2893388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893411 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2893411 : Nat := 118140960795 + 2893411 * 2 ^ 59
def prefixEnd_2893411 : Nat := 4983230072969 + 3 ^ 40 * 2893411 * 2
def baseEnd_2893411 : Nat := 1485710574006284249855951

theorem tailTrace_2893411 : CollatzResearch.WordTrace tailWord_2893411 prefixEnd_2893411 1485710574006284249855951 := by
  unfold tailWord_2893411
  simp only [CollatzResearch.WordTrace]
  refine ⟨105531368920673577102200087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70354245947115718068133391 105531368920673577102200087)
  ·
    refine ⟨158297053381010365653300131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105531368920673577102200087 158297053381010365653300131)
    ·
      refine ⟨237445580071515548479950197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158297053381010365653300131 237445580071515548479950197)
      ·
        refine ⟨22260523131704582669995331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237445580071515548479950197 22260523131704582669995331)
        ·
          refine ⟨33390784697556874004992997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22260523131704582669995331 33390784697556874004992997)
          ·
            refine ⟨6260772130791913875936187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33390784697556874004992997 6260772130791913875936187)
            ·
              refine ⟨9391158196187870813904281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6260772130791913875936187 9391158196187870813904281)
              ·
                refine ⟨7043368647140903110428211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9391158196187870813904281 7043368647140903110428211)
                ·
                  refine ⟨10565052970711354665642317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043368647140903110428211 10565052970711354665642317)
                  ·
                    refine ⟨3961894864016757999615869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10565052970711354665642317 3961894864016757999615869)
                    ·
                      refine ⟨1485710574006284249855951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3961894864016757999615869 1485710574006284249855951)
                      ·
                        rfl

theorem cell23_2893411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2893411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893411 prefixEnd_2893411 := by exact prefixLift 2893411
  have htrace : WordTrace (prefixWord ++ tailWord_2893411) baseStart_2893411 baseEnd_2893411 := by
    simpa [prefixWord, tailWord_2893411, baseEnd_2893411] using wordTrace_append hprefix tailTrace_2893411
  have hstable : (prefixWord ++ tailWord_2893411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893411).length < 2 ^ (prefixWord ++ tailWord_2893411).sum := by decide
  have hdescent : baseEnd_2893411 < baseStart_2893411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893429 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2893429 : Nat := 118140960795 + 2893429 * 2 ^ 59
def prefixEnd_2893429 : Nat := 4983230072969 + 3 ^ 40 * 2893429 * 2
def baseEnd_2893429 : Nat := 1485719816658065179430869

theorem tailTrace_2893429 : CollatzResearch.WordTrace tailWord_2893429 prefixEnd_2893429 1485719816658065179430869 := by
  unfold tailWord_2893429
  simp only [CollatzResearch.WordTrace]
  refine ⟨105532025434608366176355341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70354683623072244117570227 105532025434608366176355341)
  ·
    refine ⟨39574509537978137316133253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105532025434608366176355341 39574509537978137316133253)
    ·
      refine ⟨7420220538370900746774985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39574509537978137316133253 7420220538370900746774985)
      ·
        refine ⟨5565165403778175560081239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7420220538370900746774985 5565165403778175560081239)
        ·
          refine ⟨8347748105667263340121859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565165403778175560081239 8347748105667263340121859)
          ·
            refine ⟨12521622158500895010182789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8347748105667263340121859 12521622158500895010182789)
            ·
              refine ⟨2347804154718917814409273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12521622158500895010182789 2347804154718917814409273)
              ·
                refine ⟨1760853116039188360806955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2347804154718917814409273 1760853116039188360806955)
                ·
                  refine ⟨2641279674058782541210433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760853116039188360806955 2641279674058782541210433)
                  ·
                    refine ⟨1980959755544086905907825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641279674058782541210433 1980959755544086905907825)
                    ·
                      refine ⟨1485719816658065179430869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980959755544086905907825 1485719816658065179430869)
                      ·
                        rfl

theorem cell23_2893429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2893429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893429 prefixEnd_2893429 := by exact prefixLift 2893429
  have htrace : WordTrace (prefixWord ++ tailWord_2893429) baseStart_2893429 baseEnd_2893429 := by
    simpa [prefixWord, tailWord_2893429, baseEnd_2893429] using wordTrace_append hprefix tailTrace_2893429
  have hstable : (prefixWord ++ tailWord_2893429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893429).length < 2 ^ (prefixWord ++ tailWord_2893429).sum := by decide
  have hdescent : baseEnd_2893429 < baseStart_2893429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893472 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 1, 3, 2]
def baseStart_2893472 : Nat := 118140960795 + 2893472 * 2 ^ 59
def prefixEnd_2893472 : Nat := 4983230072969 + 3 ^ 40 * 2893472 * 2
def baseEnd_2893472 : Nat := 1485741896326208511193171

theorem tailTrace_2893472 : CollatzResearch.WordTrace tailWord_2893472 prefixEnd_2893472 1485741896326208511193171 := by
  unfold tailWord_2893472
  simp only [CollatzResearch.WordTrace]
  refine ⟨52766796886726292260085335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70355729182301723013447113 52766796886726292260085335)
  ·
    refine ⟨79150195330089438390128003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52766796886726292260085335 79150195330089438390128003)
    ·
      refine ⟨118725292995134157585192005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79150195330089438390128003 118725292995134157585192005)
      ·
        refine ⟨22260992436587654547223501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118725292995134157585192005 22260992436587654547223501)
        ·
          refine ⟨8347872163720370455208813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22260992436587654547223501 8347872163720370455208813)
          ·
            refine ⟨3130452061395138920703305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8347872163720370455208813 3130452061395138920703305)
            ·
              refine ⟨2347839046046354190527479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130452061395138920703305 2347839046046354190527479)
              ·
                refine ⟨3521758569069531285791219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347839046046354190527479 3521758569069531285791219)
                ·
                  refine ⟨5282637853604296928686829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521758569069531285791219 5282637853604296928686829)
                  ·
                    refine ⟨1980989195101611348257561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5282637853604296928686829 1980989195101611348257561)
                    ·
                      refine ⟨1485741896326208511193171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980989195101611348257561 1485741896326208511193171)
                      ·
                        rfl

theorem cell23_2893472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_2893472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893472 prefixEnd_2893472 := by exact prefixLift 2893472
  have htrace : WordTrace (prefixWord ++ tailWord_2893472) baseStart_2893472 baseEnd_2893472 := by
    simpa [prefixWord, tailWord_2893472, baseEnd_2893472] using wordTrace_append hprefix tailTrace_2893472
  have hstable : (prefixWord ++ tailWord_2893472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893472).length < 2 ^ (prefixWord ++ tailWord_2893472).sum := by decide
  have hdescent : baseEnd_2893472 < baseStart_2893472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893485 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_2893485 : Nat := 118140960795 + 2893485 * 2 ^ 59
def prefixEnd_2893485 : Nat := 4983230072969 + 3 ^ 40 * 2893485 * 2
def baseEnd_2893485 : Nat := 1485748571574716960330611

theorem tailTrace_2893485 : CollatzResearch.WordTrace tailWord_2893485 prefixEnd_2893485 1485748571574716960330611 := by
  unfold tailWord_2893485
  simp only [CollatzResearch.WordTrace]
  refine ⟨105534067922405487740393909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70356045281603658493595939 105534067922405487740393909)
  ·
    refine ⟨9893818867725514475661929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105534067922405487740393909 9893818867725514475661929)
    ·
      refine ⟨7420364150794135856746447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9893818867725514475661929 7420364150794135856746447)
      ·
        refine ⟨11130546226191203785119671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7420364150794135856746447 11130546226191203785119671)
        ·
          refine ⟨16695819339286805677679507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11130546226191203785119671 16695819339286805677679507)
          ·
            refine ⟨25043729008930208516519261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16695819339286805677679507 25043729008930208516519261)
            ·
              refine ⟨9391398378348828193694723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25043729008930208516519261 9391398378348828193694723)
              ·
                refine ⟨14087097567523242290542085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391398378348828193694723 14087097567523242290542085)
                ·
                  refine ⟨2641330793910607929476641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14087097567523242290542085 2641330793910607929476641)
                  ·
                    refine ⟨1980998095432955947107481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641330793910607929476641 1980998095432955947107481)
                    ·
                      refine ⟨1485748571574716960330611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1980998095432955947107481 1485748571574716960330611)
                      ·
                        rfl

theorem cell23_2893485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_2893485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893485 prefixEnd_2893485 := by exact prefixLift 2893485
  have htrace : WordTrace (prefixWord ++ tailWord_2893485) baseStart_2893485 baseEnd_2893485 := by
    simpa [prefixWord, tailWord_2893485, baseEnd_2893485] using wordTrace_append hprefix tailTrace_2893485
  have hstable : (prefixWord ++ tailWord_2893485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893485).length < 2 ^ (prefixWord ++ tailWord_2893485).sum := by decide
  have hdescent : baseEnd_2893485 < baseStart_2893485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893491 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 5]
def baseStart_2893491 : Nat := 118140960795 + 2893491 * 2 ^ 59
def prefixEnd_2893491 : Nat := 4983230072969 + 3 ^ 40 * 2893491 * 2
def baseEnd_2893491 : Nat := 165083516939849326317287

theorem tailTrace_2893491 : CollatzResearch.WordTrace tailWord_2893491 prefixEnd_2893491 165083516939849326317287 := by
  unfold tailWord_2893491
  simp only [CollatzResearch.WordTrace]
  refine ⟨105534286760383750765112327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70356191173589167176741551 105534286760383750765112327)
  ·
    refine ⟨158301430140575626147668491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105534286760383750765112327 158301430140575626147668491)
    ·
      refine ⟨237452145210863439221502737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158301430140575626147668491 237452145210863439221502737)
      ·
        refine ⟨178089108908147579416127053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237452145210863439221502737 178089108908147579416127053)
        ·
          refine ⟨66783415840555342281047645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178089108908147579416127053 66783415840555342281047645)
          ·
            refine ⟨25043780940208253355392867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66783415840555342281047645 25043780940208253355392867)
            ·
              refine ⟨37565671410312380033089301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25043780940208253355392867 37565671410312380033089301)
              ·
                refine ⟨1760890847358392814051061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37565671410312380033089301 1760890847358392814051061)
                ·
                  refine ⟨165083516939849326317287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1760890847358392814051061 165083516939849326317287)
                  ·
                    rfl

theorem cell23_2893491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 5].length) (baseStart_2893491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893491 prefixEnd_2893491 := by exact prefixLift 2893491
  have htrace : WordTrace (prefixWord ++ tailWord_2893491) baseStart_2893491 baseEnd_2893491 := by
    simpa [prefixWord, tailWord_2893491, baseEnd_2893491] using wordTrace_append hprefix tailTrace_2893491
  have hstable : (prefixWord ++ tailWord_2893491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893491).length < 2 ^ (prefixWord ++ tailWord_2893491).sum := by decide
  have hdescent : baseEnd_2893491 < baseStart_2893491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893501 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2893501 : Nat := 118140960795 + 2893501 * 2 ^ 59
def prefixEnd_2893501 : Nat := 4983230072969 + 3 ^ 40 * 2893501 * 2
def baseEnd_2893501 : Nat := 1485756787265188897730537

theorem tailTrace_2893501 : CollatzResearch.WordTrace tailWord_2893501 prefixEnd_2893501 1485756787265188897730537 := by
  unfold tailWord_2893501
  simp only [CollatzResearch.WordTrace]
  refine ⟨105534651490347522472976357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70356434326898348315317571 105534651490347522472976357)
  ·
    refine ⟨19787747154440160463683067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105534651490347522472976357 19787747154440160463683067)
    ·
      refine ⟨29681620731660240695524601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19787747154440160463683067 29681620731660240695524601)
      ·
        refine ⟨22261215548745180521643451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29681620731660240695524601 22261215548745180521643451)
        ·
          refine ⟨33391823323117770782465177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22261215548745180521643451 33391823323117770782465177)
          ·
            refine ⟨25043867492338328086848883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33391823323117770782465177 25043867492338328086848883)
            ·
              refine ⟨37565801238507492130273325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25043867492338328086848883 37565801238507492130273325)
              ·
                refine ⟨14087175464440309548852497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37565801238507492130273325 14087175464440309548852497)
                ·
                  refine ⟨10565381598330232161639373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14087175464440309548852497 10565381598330232161639373)
                  ·
                    refine ⟨3962018099373837060614765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10565381598330232161639373 3962018099373837060614765)
                    ·
                      refine ⟨1485756787265188897730537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962018099373837060614765 1485756787265188897730537)
                      ·
                        rfl

theorem cell23_2893501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2893501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893501 prefixEnd_2893501 := by exact prefixLift 2893501
  have htrace : WordTrace (prefixWord ++ tailWord_2893501) baseStart_2893501 baseEnd_2893501 := by
    simpa [prefixWord, tailWord_2893501, baseEnd_2893501] using wordTrace_append hprefix tailTrace_2893501
  have hstable : (prefixWord ++ tailWord_2893501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893501).length < 2 ^ (prefixWord ++ tailWord_2893501).sum := by decide
  have hdescent : baseEnd_2893501 < baseStart_2893501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893504 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_2893504 : Nat := 118140960795 + 2893504 * 2 ^ 59
def prefixEnd_2893504 : Nat := 4983230072969 + 3 ^ 40 * 2893504 * 2
def baseEnd_2893504 : Nat := 495252775902384128664341

theorem tailTrace_2893504 : CollatzResearch.WordTrace tailWord_2893504 prefixEnd_2893504 495252775902384128664341 := by
  unfold tailWord_2893504
  simp only [CollatzResearch.WordTrace]
  refine ⟨52767380454668326992667783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70356507272891102656890377 52767380454668326992667783)
  ·
    refine ⟨79151070682002490489001675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52767380454668326992667783 79151070682002490489001675)
    ·
      refine ⟨118726606023003735733502513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79151070682002490489001675 118726606023003735733502513)
      ·
        refine ⟨89044954517252801800126885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118726606023003735733502513 89044954517252801800126885)
        ·
          refine ⟨16695928971984900337523791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89044954517252801800126885 16695928971984900337523791)
          ·
            refine ⟨25043893457977350506285687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16695928971984900337523791 25043893457977350506285687)
            ·
              refine ⟨37565840186966025759428531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25043893457977350506285687 37565840186966025759428531)
              ·
                refine ⟨56348760280449038639142797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37565840186966025759428531 56348760280449038639142797)
                ·
                  refine ⟨21130785105168389489678549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56348760280449038639142797 21130785105168389489678549)
                  ·
                    refine ⟨495252775902384128664341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21130785105168389489678549 495252775902384128664341)
                    ·
                      rfl

theorem cell23_2893504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_2893504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893504 prefixEnd_2893504 := by exact prefixLift 2893504
  have htrace : WordTrace (prefixWord ++ tailWord_2893504) baseStart_2893504 baseEnd_2893504 := by
    simpa [prefixWord, tailWord_2893504, baseEnd_2893504] using wordTrace_append hprefix tailTrace_2893504
  have hstable : (prefixWord ++ tailWord_2893504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893504).length < 2 ^ (prefixWord ++ tailWord_2893504).sum := by decide
  have hdescent : baseEnd_2893504 < baseStart_2893504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893506 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2893506 : Nat := 118140960795 + 2893506 * 2 ^ 59
def prefixEnd_2893506 : Nat := 4983230072969 + 3 ^ 40 * 2893506 * 2
def baseEnd_2893506 : Nat := 1485759354668461378168015

theorem tailTrace_2893506 : CollatzResearch.WordTrace tailWord_2893506 prefixEnd_2893506 1485759354668461378168015 := by
  unfold tailWord_2893506
  simp only [CollatzResearch.WordTrace]
  refine ⟨26383708463832352081727093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70356555903552938884605581 26383708463832352081727093)
  ·
    refine ⟨2473472668484283007661915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26383708463832352081727093 2473472668484283007661915)
    ·
      refine ⟨3710209002726424511492873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2473472668484283007661915 3710209002726424511492873)
      ·
        refine ⟨2782656752044818383619655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3710209002726424511492873 2782656752044818383619655)
        ·
          refine ⟨4173985128067227575429483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782656752044818383619655 4173985128067227575429483)
          ·
            refine ⟨6260977692100841363144225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4173985128067227575429483 6260977692100841363144225)
            ·
              refine ⟨4695733269075631022358169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6260977692100841363144225 4695733269075631022358169)
              ·
                refine ⟨3521799951806723266768627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4695733269075631022358169 3521799951806723266768627)
                ·
                  refine ⟨5282699927710084900152941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3521799951806723266768627 5282699927710084900152941)
                  ·
                    refine ⟨1981012472891281837557353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5282699927710084900152941 1981012472891281837557353)
                    ·
                      refine ⟨1485759354668461378168015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981012472891281837557353 1485759354668461378168015)
                      ·
                        rfl

theorem cell23_2893506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2893506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893506 prefixEnd_2893506 := by exact prefixLift 2893506
  have htrace : WordTrace (prefixWord ++ tailWord_2893506) baseStart_2893506 baseEnd_2893506 := by
    simpa [prefixWord, tailWord_2893506, baseEnd_2893506] using wordTrace_append hprefix tailTrace_2893506
  have hstable : (prefixWord ++ tailWord_2893506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893506).length < 2 ^ (prefixWord ++ tailWord_2893506).sum := by decide
  have hdescent : baseEnd_2893506 < baseStart_2893506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893575 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2893575 : Nat := 118140960795 + 2893575 * 2 ^ 59
def prefixEnd_2893575 : Nat := 4983230072969 + 3 ^ 40 * 2893575 * 2
def baseEnd_2893575 : Nat := 1485794784833621608205197

theorem tailTrace_2893575 : CollatzResearch.WordTrace tailWord_2893575 prefixEnd_2893575 1485794784833621608205197 := by
  unfold tailWord_2893575
  simp only [CollatzResearch.WordTrace]
  refine ⟨105537350492079433111170179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70358233661386288740780119 105537350492079433111170179)
  ·
    refine ⟨158306025738119149666755269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105537350492079433111170179 158306025738119149666755269)
    ·
      refine ⟨29682379825897340562516613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158306025738119149666755269 29682379825897340562516613)
      ·
        refine ⟨5565446217355751355471865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29682379825897340562516613 5565446217355751355471865)
        ·
          refine ⟨4174084663016813516603899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5565446217355751355471865 4174084663016813516603899)
          ·
            refine ⟨6261126994525220274905849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174084663016813516603899 6261126994525220274905849)
            ·
              refine ⟨4695845245893915206179387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6261126994525220274905849 4695845245893915206179387)
              ·
                refine ⟨7043767868840872809269081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695845245893915206179387 7043767868840872809269081)
                ·
                  refine ⟨5282825901630654606951811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043767868840872809269081 5282825901630654606951811)
                  ·
                    refine ⟨7924238852445981910427717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5282825901630654606951811 7924238852445981910427717)
                    ·
                      refine ⟨1485794784833621608205197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7924238852445981910427717 1485794784833621608205197)
                      ·
                        rfl

theorem cell23_2893575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2893575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893575 prefixEnd_2893575 := by exact prefixLift 2893575
  have htrace : WordTrace (prefixWord ++ tailWord_2893575) baseStart_2893575 baseEnd_2893575 := by
    simpa [prefixWord, tailWord_2893575, baseEnd_2893575] using wordTrace_append hprefix tailTrace_2893575
  have hstable : (prefixWord ++ tailWord_2893575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893575).length < 2 ^ (prefixWord ++ tailWord_2893575).sum := by decide
  have hdescent : baseEnd_2893575 < baseStart_2893575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893578 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2893578 : Nat := 118140960795 + 2893578 * 2 ^ 59
def prefixEnd_2893578 : Nat := 4983230072969 + 3 ^ 40 * 2893578 * 2
def baseEnd_2893578 : Nat := 1485796325275585096467683

theorem tailTrace_2893578 : CollatzResearch.WordTrace tailWord_2893578 prefixEnd_2893578 1485796325275585096467683 := by
  unfold tailWord_2893578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26384364977767141155882347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70358306607379043082352925 26384364977767141155882347)
  ·
    refine ⟨39576547466650711733823521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26384364977767141155882347 39576547466650711733823521)
    ·
      refine ⟨29682410599988033800367641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39576547466650711733823521 29682410599988033800367641)
      ·
        refine ⟨22261807949991025350275731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29682410599988033800367641 22261807949991025350275731)
        ·
          refine ⟨33392711924986538025413597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22261807949991025350275731 33392711924986538025413597)
          ·
            refine ⟨12522266971869951759530099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33392711924986538025413597 12522266971869951759530099)
            ·
              refine ⟨18783400457804927639295149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12522266971869951759530099 18783400457804927639295149)
              ·
                refine ⟨7043775171676847864735681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18783400457804927639295149 7043775171676847864735681)
                ·
                  refine ⟨5282831378757635898551761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043775171676847864735681 5282831378757635898551761)
                  ·
                    refine ⟨3962123534068226923913821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5282831378757635898551761 3962123534068226923913821)
                    ·
                      refine ⟨1485796325275585096467683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962123534068226923913821 1485796325275585096467683)
                      ·
                        rfl

theorem cell23_2893578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2893578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893578 prefixEnd_2893578 := by exact prefixLift 2893578
  have htrace : WordTrace (prefixWord ++ tailWord_2893578) baseStart_2893578 baseEnd_2893578 := by
    simpa [prefixWord, tailWord_2893578, baseEnd_2893578] using wordTrace_append hprefix tailTrace_2893578
  have hstable : (prefixWord ++ tailWord_2893578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893578).length < 2 ^ (prefixWord ++ tailWord_2893578).sum := by decide
  have hdescent : baseEnd_2893578 < baseStart_2893578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893635 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 2, 3, 2]
def baseStart_2893635 : Nat := 118140960795 + 2893635 * 2 ^ 59
def prefixEnd_2893635 : Nat := 4983230072969 + 3 ^ 40 * 2893635 * 2
def baseEnd_2893635 : Nat := 1485825593672891373454921

theorem tailTrace_2893635 : CollatzResearch.WordTrace tailWord_2893635 prefixEnd_2893635 1485825593672891373454921 := by
  unfold tailWord_2893635
  simp only [CollatzResearch.WordTrace]
  refine ⟨105539538871862063358354359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70359692581241375572236239 105539538871862063358354359)
  ·
    refine ⟨158309308307793095037531539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105539538871862063358354359 158309308307793095037531539)
    ·
      refine ⟨237463962461689642556297309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158309308307793095037531539 237463962461689642556297309)
      ·
        refine ⟨89048985923133615958611491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237463962461689642556297309 89048985923133615958611491)
        ·
          refine ⟨133573478884700423937917237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89048985923133615958611491 133573478884700423937917237)
          ·
            refine ⟨12522513645440664744179741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133573478884700423937917237 12522513645440664744179741)
            ·
              refine ⟨4695942617040249279067403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12522513645440664744179741 4695942617040249279067403)
              ·
                refine ⟨7043913925560373918601105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695942617040249279067403 7043913925560373918601105)
                ·
                  refine ⟨5282935444170280438950829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043913925560373918601105 5282935444170280438950829)
                  ·
                    refine ⟨1981100791563855164606561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5282935444170280438950829 1981100791563855164606561)
                    ·
                      refine ⟨1485825593672891373454921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981100791563855164606561 1485825593672891373454921)
                      ·
                        rfl

theorem cell23_2893635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_2893635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893635 prefixEnd_2893635 := by exact prefixLift 2893635
  have htrace : WordTrace (prefixWord ++ tailWord_2893635) baseStart_2893635 baseEnd_2893635 := by
    simpa [prefixWord, tailWord_2893635, baseEnd_2893635] using wordTrace_append hprefix tailTrace_2893635
  have hstable : (prefixWord ++ tailWord_2893635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893635).length < 2 ^ (prefixWord ++ tailWord_2893635).sum := by decide
  have hdescent : baseEnd_2893635 < baseStart_2893635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893641 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_2893641 : Nat := 118140960795 + 2893641 * 2 ^ 59
def prefixEnd_2893641 : Nat := 4983230072969 + 3 ^ 40 * 2893641 * 2
def baseEnd_2893641 : Nat := 495276224852272783326631

theorem tailTrace_2893641 : CollatzResearch.WordTrace tailWord_2893641 prefixEnd_2893641 495276224852272783326631 := by
  unfold tailWord_2893641
  simp only [CollatzResearch.WordTrace]
  refine ⟨105539757709840326383072777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70359838473226884255381851 105539757709840326383072777)
  ·
    refine ⟨79154818282380244787304583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105539757709840326383072777 79154818282380244787304583)
    ·
      refine ⟨118732227423570367180956875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79154818282380244787304583 118732227423570367180956875)
      ·
        refine ⟨178098341135355550771435313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118732227423570367180956875 178098341135355550771435313)
        ·
          refine ⟨133573755851516663078576485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178098341135355550771435313 133573755851516663078576485)
          ·
            refine ⟨25045079222159374327233091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133573755851516663078576485 25045079222159374327233091)
            ·
              refine ⟨37567618833239061490849637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25045079222159374327233091 37567618833239061490849637)
              ·
                refine ⟨7043928531232324029534307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37567618833239061490849637 7043928531232324029534307)
                ·
                  refine ⟨10565892796848486044301461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043928531232324029534307 10565892796848486044301461)
                  ·
                    refine ⟨495276224852272783326631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10565892796848486044301461 495276224852272783326631)
                    ·
                      rfl

theorem cell23_2893641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_2893641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893641 prefixEnd_2893641 := by exact prefixLift 2893641
  have htrace : WordTrace (prefixWord ++ tailWord_2893641) baseStart_2893641 baseEnd_2893641 := by
    simpa [prefixWord, tailWord_2893641, baseEnd_2893641] using wordTrace_append hprefix tailTrace_2893641
  have hstable : (prefixWord ++ tailWord_2893641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893641).length < 2 ^ (prefixWord ++ tailWord_2893641).sum := by decide
  have hdescent : baseEnd_2893641 < baseStart_2893641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893642 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_2893642 : Nat := 118140960795 + 2893642 * 2 ^ 59
def prefixEnd_2893642 : Nat := 4983230072969 + 3 ^ 40 * 2893642 * 2
def baseEnd_2893642 : Nat := 1485829188037472846067389

theorem tailTrace_2893642 : CollatzResearch.WordTrace tailWord_2893642 prefixEnd_2893642 1485829188037472846067389 := by
  unfold tailWord_2893642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26384948545709175888464795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70359862788557802369239453 26384948545709175888464795)
  ·
    refine ⟨39577422818563763832697193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26384948545709175888464795 39577422818563763832697193)
    ·
      refine ⟨29683067113922822874522895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39577422818563763832697193 29683067113922822874522895)
      ·
        refine ⟨44524600670884234311784343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29683067113922822874522895 44524600670884234311784343)
        ·
          refine ⟨66786901006326351467676515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44524600670884234311784343 66786901006326351467676515)
          ·
            refine ⟨100180351509489527201514773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66786901006326351467676515 100180351509489527201514773)
            ·
              refine ⟨4695953977007321587571005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100180351509489527201514773 4695953977007321587571005)
              ·
                refine ⟨1760982741377745595339127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4695953977007321587571005 1760982741377745595339127)
                ·
                  refine ⟨2641474112066618393008691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760982741377745595339127 2641474112066618393008691)
                  ·
                    refine ⟨3962211168099927589513037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641474112066618393008691 3962211168099927589513037)
                    ·
                      refine ⟨1485829188037472846067389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962211168099927589513037 1485829188037472846067389)
                      ·
                        rfl

theorem cell23_2893642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_2893642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893642 prefixEnd_2893642 := by exact prefixLift 2893642
  have htrace : WordTrace (prefixWord ++ tailWord_2893642) baseStart_2893642 baseEnd_2893642 := by
    simpa [prefixWord, tailWord_2893642, baseEnd_2893642] using wordTrace_append hprefix tailTrace_2893642
  have hstable : (prefixWord ++ tailWord_2893642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893642).length < 2 ^ (prefixWord ++ tailWord_2893642).sum := by decide
  have hdescent : baseEnd_2893642 < baseStart_2893642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893658 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_2893658 : Nat := 118140960795 + 2893658 * 2 ^ 59
def prefixEnd_2893658 : Nat := 4983230072969 + 3 ^ 40 * 2893658 * 2
def baseEnd_2893658 : Nat := 495279134575981594489105

theorem tailTrace_2893658 : CollatzResearch.WordTrace tailWord_2893658 prefixEnd_2893658 495279134575981594489105 := by
  unfold tailWord_2893658
  simp only [CollatzResearch.WordTrace]
  refine ⟨26385094437694684571610407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70360251833852492190961085 26385094437694684571610407)
  ·
    refine ⟨39577641656542026857415611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26385094437694684571610407 39577641656542026857415611)
    ·
      refine ⟨59366462484813040286123417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39577641656542026857415611 59366462484813040286123417)
      ·
        refine ⟨44524846863609780214592563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59366462484813040286123417 44524846863609780214592563)
        ·
          refine ⟨66787270295414670321888845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44524846863609780214592563 66787270295414670321888845)
          ·
            refine ⟨25045226360780501370708317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66787270295414670321888845 25045226360780501370708317)
            ·
              refine ⟨9391959885292688014015619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25045226360780501370708317 9391959885292688014015619)
              ·
                refine ⟨14087939827939032021023429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391959885292688014015619 14087939827939032021023429)
                ·
                  refine ⟨2641488717738568503941893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14087939827939032021023429 2641488717738568503941893)
                  ·
                    refine ⟨495279134575981594489105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641488717738568503941893 495279134575981594489105)
                    ·
                      rfl

theorem cell23_2893658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_2893658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893658 prefixEnd_2893658 := by exact prefixLift 2893658
  have htrace : WordTrace (prefixWord ++ tailWord_2893658) baseStart_2893658 baseEnd_2893658 := by
    simpa [prefixWord, tailWord_2893658, baseEnd_2893658] using wordTrace_append hprefix tailTrace_2893658
  have hstable : (prefixWord ++ tailWord_2893658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893658).length < 2 ^ (prefixWord ++ tailWord_2893658).sum := by decide
  have hdescent : baseEnd_2893658 < baseStart_2893658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893671 : List Nat := [1, 1, 5, 1, 2, 1, 2, 10]
def baseStart_2893671 : Nat := 118140960795 + 2893671 * 2 ^ 59
def prefixEnd_2893671 : Nat := 4983230072969 + 3 ^ 40 * 2893671 * 2
def baseEnd_2893671 : Nat := 55031262184313082689065

theorem tailTrace_2893671 : CollatzResearch.WordTrace tailWord_2893671 prefixEnd_2893671 55031262184313082689065 := by
  unfold tailWord_2893671
  simp only [CollatzResearch.WordTrace]
  refine ⟨105540851899731641506664867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70360567933154427671109911 105540851899731641506664867)
  ·
    refine ⟨158311277849597462259997301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105540851899731641506664867 158311277849597462259997301)
    ·
      refine ⟨14841682298399762086874747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158311277849597462259997301 14841682298399762086874747)
      ·
        refine ⟨22262523447599643130312121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14841682298399762086874747 22262523447599643130312121)
        ·
          refine ⟨16696892585699732347734091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22262523447599643130312121 16696892585699732347734091)
          ·
            refine ⟨25045338878549598521601137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16696892585699732347734091 25045338878549598521601137)
            ·
              refine ⟨18784004158912198891200853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25045338878549598521601137 18784004158912198891200853)
              ·
                refine ⟨55031262184313082689065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18784004158912198891200853 55031262184313082689065)
                ·
                  rfl

theorem cell23_2893671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 10].length) (baseStart_2893671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893671 prefixEnd_2893671 := by exact prefixLift 2893671
  have htrace : WordTrace (prefixWord ++ tailWord_2893671) baseStart_2893671 baseEnd_2893671 := by
    simpa [prefixWord, tailWord_2893671, baseEnd_2893671] using wordTrace_append hprefix tailTrace_2893671
  have hstable : (prefixWord ++ tailWord_2893671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893671).length < 2 ^ (prefixWord ++ tailWord_2893671).sum := by decide
  have hdescent : baseEnd_2893671 < baseStart_2893671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893699 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 1, 2, 2]
def baseStart_2893699 : Nat := 118140960795 + 2893699 * 2 ^ 59
def prefixEnd_2893699 : Nat := 4983230072969 + 3 ^ 40 * 2893699 * 2
def baseEnd_2893699 : Nat := 1485858456434779123054627

theorem tailTrace_2893699 : CollatzResearch.WordTrace tailWord_2893699 prefixEnd_2893699 1485858456434779123054627 := by
  unfold tailWord_2893699
  simp only [CollatzResearch.WordTrace]
  refine ⟨105541873143630202288684151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70361248762420134859122767 105541873143630202288684151)
  ·
    refine ⟨158312809715445303433026227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105541873143630202288684151 158312809715445303433026227)
    ·
      refine ⟨237469214573167955149539341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158312809715445303433026227 237469214573167955149539341)
      ·
        refine ⟨89050955464937983181077253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237469214573167955149539341 89050955464937983181077253)
        ·
          refine ⟨16697054149675871846451985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89050955464937983181077253 16697054149675871846451985)
          ·
            refine ⟨12522790612256903884838989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16697054149675871846451985 12522790612256903884838989)
            ·
              refine ⟨4696046479596338956814621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12522790612256903884838989 4696046479596338956814621)
              ·
                refine ⟨1761017429848627108805483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4696046479596338956814621 1761017429848627108805483)
                ·
                  refine ⟨2641526144772940663208225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761017429848627108805483 2641526144772940663208225)
                  ·
                    refine ⟨1981144608579705497406169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641526144772940663208225 1981144608579705497406169)
                    ·
                      refine ⟨1485858456434779123054627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981144608579705497406169 1485858456434779123054627)
                      ·
                        rfl

theorem cell23_2893699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_2893699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893699 prefixEnd_2893699 := by exact prefixLift 2893699
  have htrace : WordTrace (prefixWord ++ tailWord_2893699) baseStart_2893699 baseEnd_2893699 := by
    simpa [prefixWord, tailWord_2893699, baseEnd_2893699] using wordTrace_append hprefix tailTrace_2893699
  have hstable : (prefixWord ++ tailWord_2893699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893699).length < 2 ^ (prefixWord ++ tailWord_2893699).sum := by decide
  have hdescent : baseEnd_2893699 < baseStart_2893699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893731 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 8]
def baseStart_2893731 : Nat := 118140960795 + 2893731 * 2 ^ 59
def prefixEnd_2893731 : Nat := 4983230072969 + 3 ^ 40 * 2893731 * 2
def baseEnd_2893731 : Nat := 495291629271907665951493

theorem tailTrace_2893731 : CollatzResearch.WordTrace tailWord_2893731 prefixEnd_2893731 495291629271907665951493 := by
  unfold tailWord_2893731
  simp only [CollatzResearch.WordTrace]
  refine ⟨105543040279514271753849047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70362026853009514502566031 105543040279514271753849047)
  ·
    refine ⟨158314560419271407630773571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105543040279514271753849047 158314560419271407630773571)
    ·
      refine ⟨237471840628907111446160357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158314560419271407630773571 237471840628907111446160357)
      ·
        refine ⟨44525970117920083396155067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237471840628907111446160357 44525970117920083396155067)
        ·
          refine ⟨66788955176880125094232601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44525970117920083396155067 66788955176880125094232601)
          ·
            refine ⟨50091716382660093820674451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66788955176880125094232601 50091716382660093820674451)
            ·
              refine ⟨75137574573990140731011677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50091716382660093820674451 75137574573990140731011677)
              ·
                refine ⟨28176590465246302774129379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75137574573990140731011677 28176590465246302774129379)
                ·
                  refine ⟨42264885697869454161194069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28176590465246302774129379 42264885697869454161194069)
                  ·
                    refine ⟨495291629271907665951493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42264885697869454161194069 495291629271907665951493)
                    ·
                      rfl

theorem cell23_2893731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_2893731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893731 prefixEnd_2893731 := by exact prefixLift 2893731
  have htrace : WordTrace (prefixWord ++ tailWord_2893731) baseStart_2893731 baseEnd_2893731 := by
    simpa [prefixWord, tailWord_2893731, baseEnd_2893731] using wordTrace_append hprefix tailTrace_2893731
  have hstable : (prefixWord ++ tailWord_2893731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893731).length < 2 ^ (prefixWord ++ tailWord_2893731).sum := by decide
  have hdescent : baseEnd_2893731 < baseStart_2893731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893732 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_2893732 : Nat := 118140960795 + 2893732 * 2 ^ 59
def prefixEnd_2893732 : Nat := 4983230072969 + 3 ^ 40 * 2893732 * 2
def baseEnd_2893732 : Nat := 1485875401296377493941975

theorem tailTrace_2893732 : CollatzResearch.WordTrace tailWord_2893732 prefixEnd_2893732 1485875401296377493941975 := by
  unfold tailWord_2893732
  simp only [CollatzResearch.WordTrace]
  refine ⟨52771538376255324462317725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70362051168340432616423633 52771538376255324462317725)
  ·
    refine ⟨19789326891095746673369147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52771538376255324462317725 19789326891095746673369147)
    ·
      refine ⟨29683990336643620010053721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19789326891095746673369147 29683990336643620010053721)
      ·
        refine ⟨22262992752482715007540291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29683990336643620010053721 22262992752482715007540291)
        ·
          refine ⟨33394489128724072511310437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22262992752482715007540291 33394489128724072511310437)
          ·
            refine ⟨6261466711635763595870707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33394489128724072511310437 6261466711635763595870707)
            ·
              refine ⟨9392200067453645393806061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261466711635763595870707 9392200067453645393806061)
              ·
                refine ⟨3522075025295117022677273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9392200067453645393806061 3522075025295117022677273)
                ·
                  refine ⟨2641556268971337767007955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3522075025295117022677273 2641556268971337767007955)
                  ·
                    refine ⟨3962334403457006650511933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641556268971337767007955 3962334403457006650511933)
                    ·
                      refine ⟨1485875401296377493941975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962334403457006650511933 1485875401296377493941975)
                      ·
                        rfl

theorem cell23_2893732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_2893732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893732 prefixEnd_2893732 := by exact prefixLift 2893732
  have htrace : WordTrace (prefixWord ++ tailWord_2893732) baseStart_2893732 baseEnd_2893732 := by
    simpa [prefixWord, tailWord_2893732, baseEnd_2893732] using wordTrace_append hprefix tailTrace_2893732
  have hstable : (prefixWord ++ tailWord_2893732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893732).length < 2 ^ (prefixWord ++ tailWord_2893732).sum := by decide
  have hdescent : baseEnd_2893732 < baseStart_2893732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893736 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2893736 : Nat := 118140960795 + 2893736 * 2 ^ 59
def prefixEnd_2893736 : Nat := 4983230072969 + 3 ^ 40 * 2893736 * 2
def baseEnd_2893736 : Nat := 1485877455218995478291957

theorem tailTrace_2893736 : CollatzResearch.WordTrace tailWord_2893736 prefixEnd_2893736 1485877455218995478291957 := by
  unfold tailWord_2893736
  simp only [CollatzResearch.WordTrace]
  refine ⟨52771611322248078803890531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70362148429664105071854041 52771611322248078803890531)
  ·
    refine ⟨79157416983372118205835797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52771611322248078803890531 79157416983372118205835797)
    ·
      refine ⟨3710503921095568040898553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79157416983372118205835797 3710503921095568040898553)
      ·
        refine ⟨2782877940821676030673915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3710503921095568040898553 2782877940821676030673915)
        ·
          refine ⟨4174316911232514046010873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782877940821676030673915 4174316911232514046010873)
          ·
            refine ⟨3130737683424385534508155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174316911232514046010873 3130737683424385534508155)
            ·
              refine ⟨4696106525136578301762233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130737683424385534508155 4696106525136578301762233)
              ·
                refine ⟨3522079893852433726321675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4696106525136578301762233 3522079893852433726321675)
                ·
                  refine ⟨5283119840778650589482513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522079893852433726321675 5283119840778650589482513)
                  ·
                    refine ⟨3962339880583987942111885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5283119840778650589482513 3962339880583987942111885)
                    ·
                      refine ⟨1485877455218995478291957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962339880583987942111885 1485877455218995478291957)
                      ·
                        rfl

theorem cell23_2893736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2893736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893736 prefixEnd_2893736 := by exact prefixLift 2893736
  have htrace : WordTrace (prefixWord ++ tailWord_2893736) baseStart_2893736 baseEnd_2893736 := by
    simpa [prefixWord, tailWord_2893736, baseEnd_2893736] using wordTrace_append hprefix tailTrace_2893736
  have hstable : (prefixWord ++ tailWord_2893736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893736).length < 2 ^ (prefixWord ++ tailWord_2893736).sum := by decide
  have hdescent : baseEnd_2893736 < baseStart_2893736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893782 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2893782 : Nat := 118140960795 + 2893782 * 2 ^ 59
def prefixEnd_2893782 : Nat := 4983230072969 + 3 ^ 40 * 2893782 * 2
def baseEnd_2893782 : Nat := 495300358443034099438915

theorem tailTrace_2893782 : CollatzResearch.WordTrace tailWord_2893782 prefixEnd_2893782 495300358443034099438915 := by
  unfold tailWord_2893782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596556275145594216497225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70363266934886338309303733 6596556275145594216497225)
  ·
    refine ⟨4947417206359195662372919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6596556275145594216497225 4947417206359195662372919)
    ·
      refine ⟨7421125809538793493559379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947417206359195662372919 7421125809538793493559379)
      ·
        refine ⟨11131688714308190240339069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421125809538793493559379 11131688714308190240339069)
        ·
          refine ⟨4174383267865571340127151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11131688714308190240339069 4174383267865571340127151)
          ·
            refine ⟨6261574901798357010190727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174383267865571340127151 6261574901798357010190727)
            ·
              refine ⟨9392362352697535515286091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261574901798357010190727 9392362352697535515286091)
              ·
                refine ⟨14088543529046303272929137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9392362352697535515286091 14088543529046303272929137)
                ·
                  refine ⟨10566407646784727454696853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14088543529046303272929137 10566407646784727454696853)
                  ·
                    refine ⟨495300358443034099438915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10566407646784727454696853 495300358443034099438915)
                    ·
                      rfl

theorem cell23_2893782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2893782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893782 prefixEnd_2893782 := by exact prefixLift 2893782
  have htrace : WordTrace (prefixWord ++ tailWord_2893782) baseStart_2893782 baseEnd_2893782 := by
    simpa [prefixWord, tailWord_2893782, baseEnd_2893782] using wordTrace_append hprefix tailTrace_2893782
  have hstable : (prefixWord ++ tailWord_2893782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893782).length < 2 ^ (prefixWord ++ tailWord_2893782).sum := by decide
  have hdescent : baseEnd_2893782 < baseStart_2893782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893785 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_2893785 : Nat := 118140960795 + 2893785 * 2 ^ 59
def prefixEnd_2893785 : Nat := 4983230072969 + 3 ^ 40 * 2893785 * 2
def baseEnd_2893785 : Nat := 1485902615771065786579231

theorem tailTrace_2893785 : CollatzResearch.WordTrace tailWord_2893785 prefixEnd_2893785 1485902615771065786579231 := by
  unfold tailWord_2893785
  simp only [CollatzResearch.WordTrace]
  refine ⟨105545009821318638976314809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70363339880879092650876539 105545009821318638976314809)
  ·
    refine ⟨79158757365988979232236107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105545009821318638976314809 79158757365988979232236107)
    ·
      refine ⟨118738136048983468848354161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79158757365988979232236107 118738136048983468848354161)
      ·
        refine ⟨89053602036737601636265621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118738136048983468848354161 89053602036737601636265621)
        ·
          refine ⟨4174387595472075076699951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89053602036737601636265621 4174387595472075076699951)
          ·
            refine ⟨6261581393208112615049927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174387595472075076699951 6261581393208112615049927)
            ·
              refine ⟨9392372089812168922574891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261581393208112615049927 9392372089812168922574891)
              ·
                refine ⟨14088558134718253383862337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9392372089812168922574891 14088558134718253383862337)
                ·
                  refine ⟨10566418601038690037896753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14088558134718253383862337 10566418601038690037896753)
                  ·
                    refine ⟨7924813950779017528422565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10566418601038690037896753 7924813950779017528422565)
                    ·
                      refine ⟨1485902615771065786579231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7924813950779017528422565 1485902615771065786579231)
                      ·
                        rfl

theorem cell23_2893785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_2893785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893785 prefixEnd_2893785 := by exact prefixLift 2893785
  have htrace : WordTrace (prefixWord ++ tailWord_2893785) baseStart_2893785 baseEnd_2893785 := by
    simpa [prefixWord, tailWord_2893785, baseEnd_2893785] using wordTrace_append hprefix tailTrace_2893785
  have hstable : (prefixWord ++ tailWord_2893785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893785).length < 2 ^ (prefixWord ++ tailWord_2893785).sum := by decide
  have hdescent : baseEnd_2893785 < baseStart_2893785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893789 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2893789 : Nat := 118140960795 + 2893789 * 2 ^ 59
def prefixEnd_2893789 : Nat := 4983230072969 + 3 ^ 40 * 2893789 * 2
def baseEnd_2893789 : Nat := 1485904669693683770929213

theorem tailTrace_2893789 : CollatzResearch.WordTrace tailWord_2893789 prefixEnd_2893789 1485904669693683770929213 := by
  unfold tailWord_2893789
  simp only [CollatzResearch.WordTrace]
  refine ⟨105545155713304147659460421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70363437142202765106306947 105545155713304147659460421)
  ·
    refine ⟨19789716696244527686148829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105545155713304147659460421 19789716696244527686148829)
    ·
      refine ⟨7421143761091697882305811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19789716696244527686148829 7421143761091697882305811)
      ·
        refine ⟨11131715641637546823458717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421143761091697882305811 11131715641637546823458717)
        ·
          refine ⟨4174393365614080058797019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11131715641637546823458717 4174393365614080058797019)
          ·
            refine ⟨6261590048421120088195529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174393365614080058797019 6261590048421120088195529)
            ·
              refine ⟨4696192536315840066146647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6261590048421120088195529 4696192536315840066146647)
              ·
                refine ⟨7044288804473760099219971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696192536315840066146647 7044288804473760099219971)
                ·
                  refine ⟨10566433206710640148829957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044288804473760099219971 10566433206710640148829957)
                  ·
                    refine ⟨1981206226258245027905617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10566433206710640148829957 1981206226258245027905617)
                    ·
                      refine ⟨1485904669693683770929213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981206226258245027905617 1485904669693683770929213)
                      ·
                        rfl

theorem cell23_2893789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2893789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893789 prefixEnd_2893789 := by exact prefixLift 2893789
  have htrace : WordTrace (prefixWord ++ tailWord_2893789) baseStart_2893789 baseEnd_2893789 := by
    simpa [prefixWord, tailWord_2893789, baseEnd_2893789] using wordTrace_append hprefix tailTrace_2893789
  have hstable : (prefixWord ++ tailWord_2893789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893789).length < 2 ^ (prefixWord ++ tailWord_2893789).sum := by decide
  have hdescent : baseEnd_2893789 < baseStart_2893789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893822 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2893822 : Nat := 118140960795 + 2893822 * 2 ^ 59
def prefixEnd_2893822 : Nat := 4983230072969 + 3 ^ 40 * 2893822 * 2
def baseEnd_2893822 : Nat := 1485921614555282141816561

theorem tailTrace_2893822 : CollatzResearch.WordTrace tailWord_2893822 prefixEnd_2893822 1485921614555282141816561 := by
  unfold tailWord_2893822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13193294915273074286926465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70364239548123062863607813 13193294915273074286926465)
  ·
    refine ⟨9894971186454805715194849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13193294915273074286926465 9894971186454805715194849)
    ·
      refine ⟨7421228389841104286396137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9894971186454805715194849 7421228389841104286396137)
      ·
        refine ⟨5565921292380828214797103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7421228389841104286396137 5565921292380828214797103)
        ·
          refine ⟨8348881938571242322195655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5565921292380828214797103 8348881938571242322195655)
          ·
            refine ⟨12523322907856863483293483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8348881938571242322195655 12523322907856863483293483)
            ·
              refine ⟨18784984361785295224940225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12523322907856863483293483 18784984361785295224940225)
              ·
                refine ⟨14088738271338971418705169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18784984361785295224940225 14088738271338971418705169)
                ·
                  refine ⟨10566553703504228564028877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14088738271338971418705169 10566553703504228564028877)
                  ·
                    refine ⟨3962457638814085711510829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10566553703504228564028877 3962457638814085711510829)
                    ·
                      refine ⟨1485921614555282141816561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962457638814085711510829 1485921614555282141816561)
                      ·
                        rfl

theorem cell23_2893822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2893822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893822 prefixEnd_2893822 := by exact prefixLift 2893822
  have htrace : WordTrace (prefixWord ++ tailWord_2893822) baseStart_2893822 baseEnd_2893822 := by
    simpa [prefixWord, tailWord_2893822, baseEnd_2893822] using wordTrace_append hprefix tailTrace_2893822
  have hstable : (prefixWord ++ tailWord_2893822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893822).length < 2 ^ (prefixWord ++ tailWord_2893822).sum := by decide
  have hdescent : baseEnd_2893822 < baseStart_2893822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893855 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 3, 4]
def baseStart_2893855 : Nat := 118140960795 + 2893855 * 2 ^ 59
def prefixEnd_2893855 : Nat := 4983230072969 + 3 ^ 40 * 2893855 * 2
def baseEnd_2893855 : Nat := 495312853138960170901303

theorem tailTrace_2893855 : CollatzResearch.WordTrace tailWord_2893855 prefixEnd_2893855 495312853138960170901303 := by
  unfold tailWord_2893855
  simp only [CollatzResearch.WordTrace]
  refine ⟨105547562931065040931363019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70365041954043360620908679 105547562931065040931363019)
  ·
    refine ⟨158321344396597561397044529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105547562931065040931363019 158321344396597561397044529)
    ·
      refine ⟨118741008297448171047783397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158321344396597561397044529 118741008297448171047783397)
      ·
        refine ⟨22263939055771532071459387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118741008297448171047783397 22263939055771532071459387)
        ·
          refine ⟨33395908583657298107189081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22263939055771532071459387 33395908583657298107189081)
          ·
            refine ⟨25046931437742973580391811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33395908583657298107189081 25046931437742973580391811)
            ·
              refine ⟨37570397156614460370587717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25046931437742973580391811 37570397156614460370587717)
              ·
                refine ⟨7044449466865211319485197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37570397156614460370587717 7044449466865211319485197)
                ·
                  refine ⟨2641668550074454244806949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7044449466865211319485197 2641668550074454244806949)
                  ·
                    refine ⟨495312853138960170901303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641668550074454244806949 495312853138960170901303)
                    ·
                      rfl

theorem cell23_2893855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_2893855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893855 prefixEnd_2893855 := by exact prefixLift 2893855
  have htrace : WordTrace (prefixWord ++ tailWord_2893855) baseStart_2893855 baseEnd_2893855 := by
    simpa [prefixWord, tailWord_2893855, baseEnd_2893855] using wordTrace_append hprefix tailTrace_2893855
  have hstable : (prefixWord ++ tailWord_2893855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893855).length < 2 ^ (prefixWord ++ tailWord_2893855).sum := by decide
  have hdescent : baseEnd_2893855 < baseStart_2893855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893885 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 6]
def baseStart_2893885 : Nat := 118140960795 + 2893885 * 2 ^ 59
def prefixEnd_2893885 : Nat := 4983230072969 + 3 ^ 40 * 2893885 * 2
def baseEnd_2893885 : Nat := 165105995981835043925419

theorem tailTrace_2893885 : CollatzResearch.WordTrace tailWord_2893885 prefixEnd_2893885 165105995981835043925419 := by
  unfold tailWord_2893885
  simp only [CollatzResearch.WordTrace]
  refine ⟨105548657120956356054955109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70365771413970904036636739 105548657120956356054955109)
  ·
    refine ⟨19790373210179316760304083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105548657120956356054955109 19790373210179316760304083)
    ·
      refine ⟨29685559815268975140456125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19790373210179316760304083 29685559815268975140456125)
      ·
        refine ⟨11132084930725865677671047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29685559815268975140456125 11132084930725865677671047)
        ·
          refine ⟨16698127396088798516506571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132084930725865677671047 16698127396088798516506571)
          ·
            refine ⟨25047191094133197774759857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16698127396088798516506571 25047191094133197774759857)
            ·
              refine ⟨18785393320599898331069893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25047191094133197774759857 18785393320599898331069893)
              ·
                refine ⟨3522261247612480937075605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18785393320599898331069893 3522261247612480937075605)
                ·
                  refine ⟨165105995981835043925419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3522261247612480937075605 165105995981835043925419)
                  ·
                    rfl

theorem cell23_2893885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_2893885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893885 prefixEnd_2893885 := by exact prefixLift 2893885
  have htrace : WordTrace (prefixWord ++ tailWord_2893885) baseStart_2893885 baseEnd_2893885 := by
    simpa [prefixWord, tailWord_2893885, baseEnd_2893885] using wordTrace_append hprefix tailTrace_2893885
  have hstable : (prefixWord ++ tailWord_2893885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893885).length < 2 ^ (prefixWord ++ tailWord_2893885).sum := by decide
  have hdescent : baseEnd_2893885 < baseStart_2893885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893889 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2893889 : Nat := 118140960795 + 2893889 * 2 ^ 59
def prefixEnd_2893889 : Nat := 4983230072969 + 3 ^ 40 * 2893889 * 2
def baseEnd_2893889 : Nat := 495318672586377793226251

theorem tailTrace_2893889 : CollatzResearch.WordTrace tailWord_2893889 prefixEnd_2893889 495318672586377793226251 := by
  unfold tailWord_2893889
  simp only [CollatzResearch.WordTrace]
  refine ⟨105548803012941864738100721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70365868675294576492067147 105548803012941864738100721)
  ·
    refine ⟨79161602259706398553575541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105548803012941864738100721 79161602259706398553575541)
    ·
      refine ⟨7421400211847474864397707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79161602259706398553575541 7421400211847474864397707)
      ·
        refine ⟨11132100317771212296596561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421400211847474864397707 11132100317771212296596561)
        ·
          refine ⟨8349075238328409222447421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11132100317771212296596561 8349075238328409222447421)
          ·
            refine ⟨3130903214373153458417783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8349075238328409222447421 3130903214373153458417783)
            ·
              refine ⟨4696354821559730187626675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130903214373153458417783 4696354821559730187626675)
              ·
                refine ⟨7044532232339595281440013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696354821559730187626675 7044532232339595281440013)
                ·
                  refine ⟨2641699587127348230540005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7044532232339595281440013 2641699587127348230540005)
                  ·
                    refine ⟨495318672586377793226251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641699587127348230540005 495318672586377793226251)
                    ·
                      rfl

theorem cell23_2893889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2893889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893889 prefixEnd_2893889 := by exact prefixLift 2893889
  have htrace : WordTrace (prefixWord ++ tailWord_2893889) baseStart_2893889 baseEnd_2893889 := by
    simpa [prefixWord, tailWord_2893889, baseEnd_2893889] using wordTrace_append hprefix tailTrace_2893889
  have hstable : (prefixWord ++ tailWord_2893889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893889).length < 2 ^ (prefixWord ++ tailWord_2893889).sum := by decide
  have hdescent : baseEnd_2893889 < baseStart_2893889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893898 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_2893898 : Nat := 118140960795 + 2893898 * 2 ^ 59
def prefixEnd_2893898 : Nat := 4983230072969 + 3 ^ 40 * 2893898 * 2
def baseEnd_2893898 : Nat := 495320213028341281488737

theorem tailTrace_2893898 : CollatzResearch.WordTrace tailWord_2893898 prefixEnd_2893898 495320213028341281488737 := by
  unfold tailWord_2893898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387282817477314818794587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70366087513272839516785565 26387282817477314818794587)
  ·
    refine ⟨39580924226215972228191881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26387282817477314818794587 39580924226215972228191881)
    ·
      refine ⟨29685693169661979171143911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39580924226215972228191881 29685693169661979171143911)
      ·
        refine ⟨44528539754492968756715867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29685693169661979171143911 44528539754492968756715867)
        ·
          refine ⟨66792809631739453135073801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44528539754492968756715867 66792809631739453135073801)
          ·
            refine ⟨50094607223804589851305351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66792809631739453135073801 50094607223804589851305351)
            ·
              refine ⟨75141910835706884776958027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50094607223804589851305351 75141910835706884776958027)
              ·
                refine ⟨112712866253560327165437041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75141910835706884776958027 112712866253560327165437041)
                ·
                  refine ⟨84534649690170245374077781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112712866253560327165437041 84534649690170245374077781)
                  ·
                    refine ⟨495320213028341281488737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 84534649690170245374077781 495320213028341281488737)
                    ·
                      rfl

theorem cell23_2893898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_2893898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893898 prefixEnd_2893898 := by exact prefixLift 2893898
  have htrace : WordTrace (prefixWord ++ tailWord_2893898) baseStart_2893898 baseEnd_2893898 := by
    simpa [prefixWord, tailWord_2893898, baseEnd_2893898] using wordTrace_append hprefix tailTrace_2893898
  have hstable : (prefixWord ++ tailWord_2893898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893898).length < 2 ^ (prefixWord ++ tailWord_2893898).sum := by decide
  have hdescent : baseEnd_2893898 < baseStart_2893898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893902 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_2893902 : Nat := 118140960795 + 2893902 * 2 ^ 59
def prefixEnd_2893902 : Nat := 4983230072969 + 3 ^ 40 * 2893902 * 2
def baseEnd_2893902 : Nat := 165106965889737980979577

theorem tailTrace_2893902 : CollatzResearch.WordTrace tailWord_2893902 prefixEnd_2893902 165106965889737980979577 := by
  unfold tailWord_2893902
  simp only [CollatzResearch.WordTrace]
  refine ⟨13193659645236845994790495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70366184774596511972215973 13193659645236845994790495)
  ·
    refine ⟨19790489467855268992185743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13193659645236845994790495 19790489467855268992185743)
    ·
      refine ⟨29685734201782903488278615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19790489467855268992185743 29685734201782903488278615)
      ·
        refine ⟨44528601302674355232417923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29685734201782903488278615 44528601302674355232417923)
        ·
          refine ⟨66792901954011532848626885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44528601302674355232417923 66792901954011532848626885)
          ·
            refine ⟨12523669116377162409117541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66792901954011532848626885 12523669116377162409117541)
            ·
              refine ⟨2348187959320717951709539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12523669116377162409117541 2348187959320717951709539)
              ·
                refine ⟨3522281938981076927564309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348187959320717951709539 3522281938981076927564309)
                ·
                  refine ⟨165106965889737980979577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3522281938981076927564309 165106965889737980979577)
                  ·
                    rfl

theorem cell23_2893902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_2893902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893902 prefixEnd_2893902 := by exact prefixLift 2893902
  have htrace : WordTrace (prefixWord ++ tailWord_2893902) baseStart_2893902 baseEnd_2893902 := by
    simpa [prefixWord, tailWord_2893902, baseEnd_2893902] using wordTrace_append hprefix tailTrace_2893902
  have hstable : (prefixWord ++ tailWord_2893902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893902).length < 2 ^ (prefixWord ++ tailWord_2893902).sum := by decide
  have hdescent : baseEnd_2893902 < baseStart_2893902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893929 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 1, 1, 3]
def baseStart_2893929 : Nat := 118140960795 + 2893929 * 2 ^ 59
def prefixEnd_2893929 : Nat := 4983230072969 + 3 ^ 40 * 2893929 * 2
def baseEnd_2893929 : Nat := 1485976556985313223178569

theorem tailTrace_2893929 : CollatzResearch.WordTrace tailWord_2893929 prefixEnd_2893929 1485976556985313223178569 := by
  unfold tailWord_2893929
  simp only [CollatzResearch.WordTrace]
  refine ⟨105550261932796951569556841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70366841288531301046371227 105550261932796951569556841)
  ·
    refine ⟨79162696449597713677167631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105550261932796951569556841 79162696449597713677167631)
    ·
      refine ⟨118744044674396570515751447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79162696449597713677167631 118744044674396570515751447)
      ·
        refine ⟨178116067011594855773627171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118744044674396570515751447 178116067011594855773627171)
        ·
          refine ⟨267174100517392283660440757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178116067011594855773627171 267174100517392283660440757)
          ·
            refine ⟨25047571923505526593166321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267174100517392283660440757 25047571923505526593166321)
            ·
              refine ⟨18785678942629144944874741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25047571923505526593166321 18785678942629144944874741)
              ·
                refine ⟨1761157400871482338582007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18785678942629144944874741 1761157400871482338582007)
                ·
                  refine ⟨2641736101307223507873011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761157400871482338582007 2641736101307223507873011)
                  ·
                    refine ⟨3962604151960835261809517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641736101307223507873011 3962604151960835261809517)
                    ·
                      refine ⟨1485976556985313223178569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962604151960835261809517 1485976556985313223178569)
                      ·
                        rfl

theorem cell23_2893929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 1, 3].length) (baseStart_2893929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893929 prefixEnd_2893929 := by exact prefixLift 2893929
  have htrace : WordTrace (prefixWord ++ tailWord_2893929) baseStart_2893929 baseEnd_2893929 := by
    simpa [prefixWord, tailWord_2893929, baseEnd_2893929] using wordTrace_append hprefix tailTrace_2893929
  have hstable : (prefixWord ++ tailWord_2893929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893929).length < 2 ^ (prefixWord ++ tailWord_2893929).sum := by decide
  have hdescent : baseEnd_2893929 < baseStart_2893929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893962 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_2893962 : Nat := 118140960795 + 2893962 * 2 ^ 59
def prefixEnd_2893962 : Nat := 4983230072969 + 3 ^ 40 * 2893962 * 2
def baseEnd_2893962 : Nat := 495331167282303864688639

theorem tailTrace_2893962 : CollatzResearch.WordTrace tailWord_2893962 prefixEnd_2893962 495331167282303864688639 := by
  unfold tailWord_2893962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26387866385419349551377035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70367643694451598803672093 26387866385419349551377035)
  ·
    refine ⟨39581799578129024327065553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26387866385419349551377035 39581799578129024327065553)
    ·
      refine ⟨29686349683596768245299165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39581799578129024327065553 29686349683596768245299165)
      ·
        refine ⟨11132381131348788091987187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29686349683596768245299165 11132381131348788091987187)
        ·
          refine ⟨16698571697023182137980781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132381131348788091987187 16698571697023182137980781)
          ·
            refine ⟨6261964386383693301742793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16698571697023182137980781 6261964386383693301742793)
            ·
              refine ⟨4696473289787769976307095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6261964386383693301742793 4696473289787769976307095)
              ·
                refine ⟨7044709934681654964460643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696473289787769976307095 7044709934681654964460643)
                ·
                  refine ⟨10567064902022482446690965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7044709934681654964460643 10567064902022482446690965)
                  ·
                    refine ⟨495331167282303864688639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10567064902022482446690965 495331167282303864688639)
                    ·
                      rfl

theorem cell23_2893962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_2893962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893962 prefixEnd_2893962 := by exact prefixLift 2893962
  have htrace : WordTrace (prefixWord ++ tailWord_2893962) baseStart_2893962 baseEnd_2893962 := by
    simpa [prefixWord, tailWord_2893962, baseEnd_2893962] using wordTrace_append hprefix tailTrace_2893962
  have hstable : (prefixWord ++ tailWord_2893962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893962).length < 2 ^ (prefixWord ++ tailWord_2893962).sum := by decide
  have hdescent : baseEnd_2893962 < baseStart_2893962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2893986 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2893986 : Nat := 118140960795 + 2893986 * 2 ^ 59
def prefixEnd_2893986 : Nat := 4983230072969 + 3 ^ 40 * 2893986 * 2
def baseEnd_2893986 : Nat := 1486005825382619500165807

theorem tailTrace_2893986 : CollatzResearch.WordTrace tailWord_2893986 prefixEnd_2893986 1486005825382619500165807 := by
  unfold tailWord_2893986
  simp only [CollatzResearch.WordTrace]
  refine ⟨26388085223397612576095453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70368227262393633536254541 26388085223397612576095453)
  ·
    refine ⟨9895531958774104716035795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26388085223397612576095453 9895531958774104716035795)
    ·
      refine ⟨14843297938161157074053693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9895531958774104716035795 14843297938161157074053693)
      ·
        refine ⟨5566236726810433902770135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14843297938161157074053693 5566236726810433902770135)
        ·
          refine ⟨8349355090215650854155203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566236726810433902770135 8349355090215650854155203)
          ·
            refine ⟨12524032635323476281232805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8349355090215650854155203 12524032635323476281232805)
            ·
              refine ⟨2348256119123151802731151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12524032635323476281232805 2348256119123151802731151)
              ·
                refine ⟨3522384178684727704096727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348256119123151802731151 3522384178684727704096727)
                ·
                  refine ⟨5283576268027091556145091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522384178684727704096727 5283576268027091556145091)
                  ·
                    refine ⟨7925364402040637334217637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5283576268027091556145091 7925364402040637334217637)
                    ·
                      refine ⟨1486005825382619500165807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7925364402040637334217637 1486005825382619500165807)
                      ·
                        rfl

theorem cell23_2893986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2893986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2893986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2893986 prefixEnd_2893986 := by exact prefixLift 2893986
  have htrace : WordTrace (prefixWord ++ tailWord_2893986) baseStart_2893986 baseEnd_2893986 := by
    simpa [prefixWord, tailWord_2893986, baseEnd_2893986] using wordTrace_append hprefix tailTrace_2893986
  have hstable : (prefixWord ++ tailWord_2893986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2893986).length < 2 ^ (prefixWord ++ tailWord_2893986).sum := by decide
  have hdescent : baseEnd_2893986 < baseStart_2893986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2893986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894037 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2894037 : Nat := 118140960795 + 2894037 * 2 ^ 59
def prefixEnd_2894037 : Nat := 4983230072969 + 3 ^ 40 * 2894037 * 2
def baseEnd_2894037 : Nat := 1486032012895998800628073

theorem tailTrace_2894037 : CollatzResearch.WordTrace tailWord_2894037 prefixEnd_2894037 1486032012895998800628073 := by
  unfold tailWord_2894037
  simp only [CollatzResearch.WordTrace]
  refine ⟨105554201016405686014488365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70369467344270457342992243 105554201016405686014488365)
  ·
    refine ⟨39582825381152132255433137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105554201016405686014488365 39582825381152132255433137)
    ·
      refine ⟨29687119035864099191574853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39582825381152132255433137 29687119035864099191574853)
      ·
        refine ⟨5566334819224518598420285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29687119035864099191574853 5566334819224518598420285)
        ·
          refine ⟨2087375557209194474407607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5566334819224518598420285 2087375557209194474407607)
          ·
            refine ⟨3131063335813791711611411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087375557209194474407607 3131063335813791711611411)
            ·
              refine ⟨4696595003720687567417117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131063335813791711611411 4696595003720687567417117)
              ·
                refine ⟨1761223126395257837781419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4696595003720687567417117 1761223126395257837781419)
                ·
                  refine ⟨2641834689592886756672129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761223126395257837781419 2641834689592886756672129)
                  ·
                    refine ⟨1981376017194665067504097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641834689592886756672129 1981376017194665067504097)
                    ·
                      refine ⟨1486032012895998800628073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981376017194665067504097 1486032012895998800628073)
                      ·
                        rfl

theorem cell23_2894037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2894037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894037 prefixEnd_2894037 := by exact prefixLift 2894037
  have htrace : WordTrace (prefixWord ++ tailWord_2894037) baseStart_2894037 baseEnd_2894037 := by
    simpa [prefixWord, tailWord_2894037, baseEnd_2894037] using wordTrace_append hprefix tailTrace_2894037
  have hstable : (prefixWord ++ tailWord_2894037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894037).length < 2 ^ (prefixWord ++ tailWord_2894037).sum := by decide
  have hdescent : baseEnd_2894037 < baseStart_2894037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894059 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 4, 2, 2]
def baseStart_2894059 : Nat := 118140960795 + 2894059 * 2 ^ 59
def prefixEnd_2894059 : Nat := 4983230072969 + 3 ^ 40 * 2894059 * 2
def baseEnd_2894059 : Nat := 1486043309470397714552971

theorem tailTrace_2894059 : CollatzResearch.WordTrace tailWord_2894059 prefixEnd_2894059 1486043309470397714552971 := by
  unfold tailWord_2894059
  simp only [CollatzResearch.WordTrace]
  refine ⟨105555003422325983771789231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70370002281550655847859487 105555003422325983771789231)
  ·
    refine ⟨158332505133488975657683847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105555003422325983771789231 158332505133488975657683847)
    ·
      refine ⟨237498757700233463486525771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158332505133488975657683847 237498757700233463486525771)
      ·
        refine ⟨356248136550350195229788657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237498757700233463486525771 356248136550350195229788657)
        ·
          refine ⟨267186102412762646422341493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356248136550350195229788657 267186102412762646422341493)
          ·
            refine ⟨25048697101196498102094515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267186102412762646422341493 25048697101196498102094515)
            ·
              refine ⟨37573045651794747153141773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25048697101196498102094515 37573045651794747153141773)
              ·
                refine ⟨14089892119423030182428165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37573045651794747153141773 14089892119423030182428165)
                ·
                  refine ⟨2641854772391818159205281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14089892119423030182428165 2641854772391818159205281)
                  ·
                    refine ⟨1981391079293863619403961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641854772391818159205281 1981391079293863619403961)
                    ·
                      refine ⟨1486043309470397714552971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981391079293863619403961 1486043309470397714552971)
                      ·
                        rfl

theorem cell23_2894059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 2, 2].length) (baseStart_2894059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894059 prefixEnd_2894059 := by exact prefixLift 2894059
  have htrace : WordTrace (prefixWord ++ tailWord_2894059) baseStart_2894059 baseEnd_2894059 := by
    simpa [prefixWord, tailWord_2894059, baseEnd_2894059] using wordTrace_append hprefix tailTrace_2894059
  have hstable : (prefixWord ++ tailWord_2894059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894059).length < 2 ^ (prefixWord ++ tailWord_2894059).sum := by decide
  have hdescent : baseEnd_2894059 < baseStart_2894059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894062 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_2894062 : Nat := 118140960795 + 2894062 * 2 ^ 59
def prefixEnd_2894062 : Nat := 4983230072969 + 3 ^ 40 * 2894062 * 2
def baseEnd_2894062 : Nat := 1486044849912361202815457

theorem tailTrace_2894062 : CollatzResearch.WordTrace tailWord_2894062 prefixEnd_2894062 1486044849912361202815457 := by
  unfold tailWord_2894062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13194389105164389410518555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70370075227543410189432293 13194389105164389410518555)
  ·
    refine ⟨19791583657746584115777833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13194389105164389410518555 19791583657746584115777833)
    ·
      refine ⟨14843687743309938086833375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19791583657746584115777833 14843687743309938086833375)
      ·
        refine ⟨22265531614964907130250063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14843687743309938086833375 22265531614964907130250063)
        ·
          refine ⟨33398297422447360695375095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22265531614964907130250063 33398297422447360695375095)
          ·
            refine ⟨50097446133671041043062643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33398297422447360695375095 50097446133671041043062643)
            ·
              refine ⟨75146169200506561564593965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50097446133671041043062643 75146169200506561564593965)
              ·
                refine ⟨28179813450189960586722737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75146169200506561564593965 28179813450189960586722737)
                ·
                  refine ⟨21134860087642470440042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28179813450189960586722737 21134860087642470440042053)
                  ·
                    refine ⟨3962786266432963207507885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21134860087642470440042053 3962786266432963207507885)
                    ·
                      refine ⟨1486044849912361202815457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962786266432963207507885 1486044849912361202815457)
                      ·
                        rfl

theorem cell23_2894062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_2894062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894062 prefixEnd_2894062 := by exact prefixLift 2894062
  have htrace : WordTrace (prefixWord ++ tailWord_2894062) baseStart_2894062 baseEnd_2894062 := by
    simpa [prefixWord, tailWord_2894062, baseEnd_2894062] using wordTrace_append hprefix tailTrace_2894062
  have hstable : (prefixWord ++ tailWord_2894062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894062).length < 2 ^ (prefixWord ++ tailWord_2894062).sum := by decide
  have hdescent : baseEnd_2894062 < baseStart_2894062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894095 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 1, 7]
def baseStart_2894095 : Nat := 118140960795 + 2894095 * 2 ^ 59
def prefixEnd_2894095 : Nat := 4983230072969 + 3 ^ 40 * 2894095 * 2
def baseEnd_2894095 : Nat := 495353931591319857900935

theorem tailTrace_2894095 : CollatzResearch.WordTrace tailWord_2894095 prefixEnd_2894095 495353931591319857900935 := by
  unfold tailWord_2894095
  simp only [CollatzResearch.WordTrace]
  refine ⟨105556316450195561920099739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70370877633463707946733159 105556316450195561920099739)
  ·
    refine ⟨158334474675293342880149609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105556316450195561920099739 158334474675293342880149609)
    ·
      refine ⟨118750856006470007160112207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158334474675293342880149609 118750856006470007160112207)
      ·
        refine ⟨178126284009705010740168311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118750856006470007160112207 178126284009705010740168311)
        ·
          refine ⟨267189426014557516110252467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178126284009705010740168311 267189426014557516110252467)
          ·
            refine ⟨400784139021836274165378701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267189426014557516110252467 400784139021836274165378701)
            ·
              refine ⟨150294052133188602812017013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400784139021836274165378701 150294052133188602812017013)
              ·
                refine ⟨14090067387486431513626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150294052133188602812017013 14090067387486431513626595)
                ·
                  refine ⟨21135101081229647270439893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14090067387486431513626595 21135101081229647270439893)
                  ·
                    refine ⟨495353931591319857900935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21135101081229647270439893 495353931591319857900935)
                    ·
                      rfl

theorem cell23_2894095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_2894095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894095 prefixEnd_2894095 := by exact prefixLift 2894095
  have htrace : WordTrace (prefixWord ++ tailWord_2894095) baseStart_2894095 baseEnd_2894095 := by
    simpa [prefixWord, tailWord_2894095, baseEnd_2894095] using wordTrace_append hprefix tailTrace_2894095
  have hstable : (prefixWord ++ tailWord_2894095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894095).length < 2 ^ (prefixWord ++ tailWord_2894095).sum := by decide
  have hdescent : baseEnd_2894095 < baseStart_2894095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894110 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2894110 : Nat := 118140960795 + 2894110 * 2 ^ 59
def prefixEnd_2894110 : Nat := 4983230072969 + 3 ^ 40 * 2894110 * 2
def baseEnd_2894110 : Nat := 1486069496983777015015237

theorem tailTrace_2894110 : CollatzResearch.WordTrace tailWord_2894110 prefixEnd_2894110 1486069496983777015015237 := by
  unfold tailWord_2894110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13194607943142652435236973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70371242363427479654597189 13194607943142652435236973)
  ·
    refine ⟨4947977978678494663213865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13194607943142652435236973 4947977978678494663213865)
    ·
      refine ⟨3710983484008870997410399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4947977978678494663213865 3710983484008870997410399)
      ·
        refine ⟨5566475226013306496115599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3710983484008870997410399 5566475226013306496115599)
        ·
          refine ⟨8349712839019959744173399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566475226013306496115599 8349712839019959744173399)
          ·
            refine ⟨12524569258529939616260099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8349712839019959744173399 12524569258529939616260099)
            ·
              refine ⟨18786853887794909424390149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12524569258529939616260099 18786853887794909424390149)
              ·
                refine ⟨3522535103961545517073153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18786853887794909424390149 3522535103961545517073153)
                ·
                  refine ⟨2641901327971159137804865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3522535103961545517073153 2641901327971159137804865)
                  ·
                    refine ⟨1981425995978369353353649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2641901327971159137804865 1981425995978369353353649)
                    ·
                      refine ⟨1486069496983777015015237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981425995978369353353649 1486069496983777015015237)
                      ·
                        rfl

theorem cell23_2894110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2894110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894110 prefixEnd_2894110 := by exact prefixLift 2894110
  have htrace : WordTrace (prefixWord ++ tailWord_2894110) baseStart_2894110 baseEnd_2894110 := by
    simpa [prefixWord, tailWord_2894110, baseEnd_2894110] using wordTrace_append hprefix tailTrace_2894110
  have hstable : (prefixWord ++ tailWord_2894110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894110).length < 2 ^ (prefixWord ++ tailWord_2894110).sum := by decide
  have hdescent : baseEnd_2894110 < baseStart_2894110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894116 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 5]
def baseStart_2894116 : Nat := 118140960795 + 2894116 * 2 ^ 59
def prefixEnd_2894116 : Nat := 4983230072969 + 3 ^ 40 * 2894116 * 2
def baseEnd_2894116 : Nat := 165119175318633776837801

theorem tailTrace_2894116 : CollatzResearch.WordTrace tailWord_2894116 prefixEnd_2894116 165119175318633776837801 := by
  unfold tailWord_2894116
  simp only [CollatzResearch.WordTrace]
  refine ⟨52778541191559741253307101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70371388255412988337742801 52778541191559741253307101)
  ·
    refine ⟨19791952946834902969990163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52778541191559741253307101 19791952946834902969990163)
    ·
      refine ⟨29687929420252354454985245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19791952946834902969990163 29687929420252354454985245)
      ·
        refine ⟨11132973532594632920619467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29687929420252354454985245 11132973532594632920619467)
        ·
          refine ⟨16699460298891949380929201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11132973532594632920619467 16699460298891949380929201)
          ·
            refine ⟨12524595224168962035696901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16699460298891949380929201 12524595224168962035696901)
            ·
              refine ⟨2348361604531680381693169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12524595224168962035696901 2348361604531680381693169)
              ·
                refine ⟨1761271203398760286269877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348361604531680381693169 1761271203398760286269877)
                ·
                  refine ⟨165119175318633776837801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1761271203398760286269877 165119175318633776837801)
                  ·
                    rfl

theorem cell23_2894116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_2894116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894116 prefixEnd_2894116 := by exact prefixLift 2894116
  have htrace : WordTrace (prefixWord ++ tailWord_2894116) baseStart_2894116 baseEnd_2894116 := by
    simpa [prefixWord, tailWord_2894116, baseEnd_2894116] using wordTrace_append hprefix tailTrace_2894116
  have hstable : (prefixWord ++ tailWord_2894116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894116).length < 2 ^ (prefixWord ++ tailWord_2894116).sum := by decide
  have hdescent : baseEnd_2894116 < baseStart_2894116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894162 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2894162 : Nat := 118140960795 + 2894162 * 2 ^ 59
def prefixEnd_2894162 : Nat := 4983230072969 + 3 ^ 40 * 2894162 * 2
def baseEnd_2894162 : Nat := 1486096197977810811564997

theorem tailTrace_2894162 : CollatzResearch.WordTrace tailWord_2894162 prefixEnd_2894162 1486096197977810811564997 := by
  unfold tailWord_2894162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26389690035238208090697185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70372506760635221575192493 26389690035238208090697185)
  ·
    refine ⟨19792267526428656068022889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26389690035238208090697185 19792267526428656068022889)
    ·
      refine ⟨14844200644821492051017167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19792267526428656068022889 14844200644821492051017167)
      ·
        refine ⟨22266300967232238076525751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14844200644821492051017167 22266300967232238076525751)
        ·
          refine ⟨33399451450848357114788627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22266300967232238076525751 33399451450848357114788627)
          ·
            refine ⟨50099177176272535672182941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33399451450848357114788627 50099177176272535672182941)
            ·
              refine ⟨18787191441102200877068603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50099177176272535672182941 18787191441102200877068603)
              ·
                refine ⟨28180787161653301315602905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18787191441102200877068603 28180787161653301315602905)
                ·
                  refine ⟨21135590371239975986702179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28180787161653301315602905 21135590371239975986702179)
                  ·
                    refine ⟨31703385556859963980053269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21135590371239975986702179 31703385556859963980053269)
                    ·
                      refine ⟨1486096197977810811564997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31703385556859963980053269 1486096197977810811564997)
                      ·
                        rfl

theorem cell23_2894162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2894162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894162 prefixEnd_2894162 := by exact prefixLift 2894162
  have htrace : WordTrace (prefixWord ++ tailWord_2894162) baseStart_2894162 baseEnd_2894162 := by
    simpa [prefixWord, tailWord_2894162, baseEnd_2894162] using wordTrace_append hprefix tailTrace_2894162
  have hstable : (prefixWord ++ tailWord_2894162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894162).length < 2 ^ (prefixWord ++ tailWord_2894162).sum := by decide
  have hdescent : baseEnd_2894162 < baseStart_2894162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894176 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 3, 4]
def baseStart_2894176 : Nat := 118140960795 + 2894176 * 2 ^ 59
def prefixEnd_2894176 : Nat := 4983230072969 + 3 ^ 40 * 2894176 * 2
def baseEnd_2894176 : Nat := 495367795568991252263311

theorem tailTrace_2894176 : CollatzResearch.WordTrace tailWord_2894176 prefixEnd_2894176 495367795568991252263311 := by
  unfold tailWord_2894176
  simp only [CollatzResearch.WordTrace]
  refine ⟨52779635381451056376899191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70372847175268075169198921 52779635381451056376899191)
  ·
    refine ⟨79169453072176584565348787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52779635381451056376899191 79169453072176584565348787)
    ·
      refine ⟨118754179608264876848023181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79169453072176584565348787 118754179608264876848023181)
      ·
        refine ⟨44532817353099328818008693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118754179608264876848023181 44532817353099328818008693)
        ·
          refine ⟨4174951626853062076688315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44532817353099328818008693 4174951626853062076688315)
          ·
            refine ⟨6262427440279593115032473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174951626853062076688315 6262427440279593115032473)
            ·
              refine ⟨4696820580209694836274355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6262427440279593115032473 4696820580209694836274355)
              ·
                refine ⟨7045230870314542254411533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4696820580209694836274355 7045230870314542254411533)
                ·
                  refine ⟨2641961576367953345404325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7045230870314542254411533 2641961576367953345404325)
                  ·
                    refine ⟨495367795568991252263311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2641961576367953345404325 495367795568991252263311)
                    ·
                      rfl

theorem cell23_2894176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_2894176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894176 prefixEnd_2894176 := by exact prefixLift 2894176
  have htrace : WordTrace (prefixWord ++ tailWord_2894176) baseStart_2894176 baseEnd_2894176 := by
    simpa [prefixWord, tailWord_2894176, baseEnd_2894176] using wordTrace_append hprefix tailTrace_2894176
  have hstable : (prefixWord ++ tailWord_2894176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894176).length < 2 ^ (prefixWord ++ tailWord_2894176).sum := by decide
  have hdescent : baseEnd_2894176 < baseStart_2894176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894199 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_2894199 : Nat := 118140960795 + 2894199 * 2 ^ 59
def prefixEnd_2894199 : Nat := 4983230072969 + 3 ^ 40 * 2894199 * 2
def baseEnd_2894199 : Nat := 1486115196762027166802327

theorem tailTrace_2894199 : CollatzResearch.WordTrace tailWord_2894199 prefixEnd_2894199 1486115196762027166802327 := by
  unfold tailWord_2894199
  simp only [CollatzResearch.WordTrace]
  refine ⟨105560109641818787681885651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70373406427879191787923767 105560109641818787681885651)
  ·
    refine ⟨158340164462728181522828477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105560109641818787681885651 158340164462728181522828477)
    ·
      refine ⟨59377561673523068071060679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158340164462728181522828477 59377561673523068071060679)
      ·
        refine ⟨89066342510284602106591019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59377561673523068071060679 89066342510284602106591019)
        ·
          refine ⟨133599513765426903159886529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89066342510284602106591019 133599513765426903159886529)
          ·
            refine ⟨100199635324070177369914897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133599513765426903159886529 100199635324070177369914897)
            ·
              refine ⟨75149726493052633027436173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100199635324070177369914897 75149726493052633027436173)
              ·
                refine ⟨28181147434894737385288565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75149726493052633027436173 28181147434894737385288565)
                ·
                  refine ⟨2641982572021381629870803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28181147434894737385288565 2641982572021381629870803)
                  ·
                    refine ⟨3962973858032072444806205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2641982572021381629870803 3962973858032072444806205)
                    ·
                      refine ⟨1486115196762027166802327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3962973858032072444806205 1486115196762027166802327)
                      ·
                        rfl

theorem cell23_2894199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_2894199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894199 prefixEnd_2894199 := by exact prefixLift 2894199
  have htrace : WordTrace (prefixWord ++ tailWord_2894199) baseStart_2894199 baseEnd_2894199 := by
    simpa [prefixWord, tailWord_2894199, baseEnd_2894199] using wordTrace_append hprefix tailTrace_2894199
  have hstable : (prefixWord ++ tailWord_2894199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894199).length < 2 ^ (prefixWord ++ tailWord_2894199).sum := by decide
  have hdescent : baseEnd_2894199 < baseStart_2894199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894219 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 1, 5]
def baseStart_2894219 : Nat := 118140960795 + 2894219 * 2 ^ 59
def prefixEnd_2894219 : Nat := 4983230072969 + 3 ^ 40 * 2894219 * 2
def baseEnd_2894219 : Nat := 495375155458372362850745

theorem tailTrace_2894219 : CollatzResearch.WordTrace tailWord_2894219 prefixEnd_2894219 495375155458372362850745 := by
  unfold tailWord_2894219
  simp only [CollatzResearch.WordTrace]
  refine ⟨105560839101746331097613711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70373892734497554065075807 105560839101746331097613711)
  ·
    refine ⟨158341258652619496646420567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105560839101746331097613711 158341258652619496646420567)
    ·
      refine ⟨237511887978929244969630851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158341258652619496646420567 237511887978929244969630851)
      ·
        refine ⟨356267831968393867454446277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237511887978929244969630851 356267831968393867454446277)
        ·
          refine ⟨66800218494073850147708677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 356267831968393867454446277 66800218494073850147708677)
          ·
            refine ⟨12525040967638846902695377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66800218494073850147708677 12525040967638846902695377)
            ·
              refine ⟨9393780725729135177021533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12525040967638846902695377 9393780725729135177021533)
              ·
                refine ⟨3522667772148425691383075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9393780725729135177021533 3522667772148425691383075)
                ·
                  refine ⟨5284001658222638537074613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522667772148425691383075 5284001658222638537074613)
                  ·
                    refine ⟨495375155458372362850745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5284001658222638537074613 495375155458372362850745)
                    ·
                      rfl

theorem cell23_2894219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 5].length) (baseStart_2894219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894219 prefixEnd_2894219 := by exact prefixLift 2894219
  have htrace : WordTrace (prefixWord ++ tailWord_2894219) baseStart_2894219 baseEnd_2894219 := by
    simpa [prefixWord, tailWord_2894219, baseEnd_2894219] using wordTrace_append hprefix tailTrace_2894219
  have hstable : (prefixWord ++ tailWord_2894219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894219).length < 2 ^ (prefixWord ++ tailWord_2894219).sum := by decide
  have hdescent : baseEnd_2894219 < baseStart_2894219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894239 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2894239 : Nat := 118140960795 + 2894239 * 2 ^ 59
def prefixEnd_2894239 : Nat := 4983230072969 + 3 ^ 40 * 2894239 * 2
def baseEnd_2894239 : Nat := 1486135735988207010302143

theorem tailTrace_2894239 : CollatzResearch.WordTrace tailWord_2894239 prefixEnd_2894239 1486135735988207010302143 := by
  unfold tailWord_2894239
  simp only [CollatzResearch.WordTrace]
  refine ⟨105561568561673874513341771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70374379041115916342227847 105561568561673874513341771)
  ·
    refine ⟨158342352842510811770012657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105561568561673874513341771 158342352842510811770012657)
    ·
      refine ⟨118756764631883108827509493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158342352842510811770012657 118756764631883108827509493)
      ·
        refine ⟨11133446684239041452579015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118756764631883108827509493 11133446684239041452579015)
        ·
          refine ⟨16700170026358562178868523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11133446684239041452579015 16700170026358562178868523)
          ·
            refine ⟨25050255039537843268302785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16700170026358562178868523 25050255039537843268302785)
            ·
              refine ⟨18787691279653382451227089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25050255039537843268302785 18787691279653382451227089)
              ·
                refine ⟨14090768459740036838420317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18787691279653382451227089 14090768459740036838420317)
                ·
                  refine ⟨5284038172402513814407619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14090768459740036838420317 5284038172402513814407619)
                  ·
                    refine ⟨7926057258603770721611429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5284038172402513814407619 7926057258603770721611429)
                    ·
                      refine ⟨1486135735988207010302143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7926057258603770721611429 1486135735988207010302143)
                      ·
                        rfl

theorem cell23_2894239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2894239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894239 prefixEnd_2894239 := by exact prefixLift 2894239
  have htrace : WordTrace (prefixWord ++ tailWord_2894239) baseStart_2894239 baseEnd_2894239 := by
    simpa [prefixWord, tailWord_2894239, baseEnd_2894239] using wordTrace_append hprefix tailTrace_2894239
  have hstable : (prefixWord ++ tailWord_2894239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894239).length < 2 ^ (prefixWord ++ tailWord_2894239).sum := by decide
  have hdescent : baseEnd_2894239 < baseStart_2894239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894269 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2894269 : Nat := 118140960795 + 2894269 * 2 ^ 59
def prefixEnd_2894269 : Nat := 4983230072969 + 3 ^ 40 * 2894269 * 2
def baseEnd_2894269 : Nat := 1486151140407841892927005

theorem tailTrace_2894269 : CollatzResearch.WordTrace tailWord_2894269 prefixEnd_2894269 1486151140407841892927005 := by
  unfold tailWord_2894269
  simp only [CollatzResearch.WordTrace]
  refine ⟨105562662751565189636933861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70375108501043459757955907 105562662751565189636933861)
  ·
    refine ⟨19792999265918473056925099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105562662751565189636933861 19792999265918473056925099)
    ·
      refine ⟨29689498898877709585387649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19792999265918473056925099 29689498898877709585387649)
      ·
        refine ⟨22267124174158282189040737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29689498898877709585387649 22267124174158282189040737)
        ·
          refine ⟨16700343130618711641780553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22267124174158282189040737 16700343130618711641780553)
          ·
            refine ⟨12525257347964033731335415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16700343130618711641780553 12525257347964033731335415)
            ·
              refine ⟨18787886021946050597003123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12525257347964033731335415 18787886021946050597003123)
              ·
                refine ⟨28181829032919075895504685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18787886021946050597003123 28181829032919075895504685)
                ·
                  refine ⟨10568185887344653460814257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28181829032919075895504685 10568185887344653460814257)
                  ·
                    refine ⟨7926139415508490095610693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10568185887344653460814257 7926139415508490095610693)
                    ·
                      refine ⟨1486151140407841892927005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7926139415508490095610693 1486151140407841892927005)
                      ·
                        rfl

theorem cell23_2894269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2894269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894269 prefixEnd_2894269 := by exact prefixLift 2894269
  have htrace : WordTrace (prefixWord ++ tailWord_2894269) baseStart_2894269 baseEnd_2894269 := by
    simpa [prefixWord, tailWord_2894269, baseEnd_2894269] using wordTrace_append hprefix tailTrace_2894269
  have hstable : (prefixWord ++ tailWord_2894269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894269).length < 2 ^ (prefixWord ++ tailWord_2894269).sum := by decide
  have hdescent : baseEnd_2894269 < baseStart_2894269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894284 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 1, 1, 3]
def baseStart_2894284 : Nat := 118140960795 + 2894284 * 2 ^ 59
def prefixEnd_2894284 : Nat := 4983230072969 + 3 ^ 40 * 2894284 * 2
def baseEnd_2894284 : Nat := 1486158842617659334239437

theorem tailTrace_2894284 : CollatzResearch.WordTrace tailWord_2894284 prefixEnd_2894284 1486158842617659334239437 := by
  unfold tailWord_2894284
  simp only [CollatzResearch.WordTrace]
  refine ⟨52781604923255423599364953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70375473231007231465819937 52781604923255423599364953)
  ·
    refine ⟨39586203692441567699523715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52781604923255423599364953 39586203692441567699523715)
    ·
      refine ⟨59379305538662351549285573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39586203692441567699523715 59379305538662351549285573)
      ·
        refine ⟨11133619788499190915491045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59379305538662351549285573 11133619788499190915491045)
        ·
          refine ⟨2087553710343598296654571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11133619788499190915491045 2087553710343598296654571)
          ·
            refine ⟨3131330565515397444981857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087553710343598296654571 3131330565515397444981857)
            ·
              refine ⟨2348497924136548083736393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131330565515397444981857 2348497924136548083736393)
              ·
                refine ⟨1761373443102411062802295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348497924136548083736393 1761373443102411062802295)
                ·
                  refine ⟨2642060164653616594203443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761373443102411062802295 2642060164653616594203443)
                  ·
                    refine ⟨3963090246980424891305165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2642060164653616594203443 3963090246980424891305165)
                    ·
                      refine ⟨1486158842617659334239437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963090246980424891305165 1486158842617659334239437)
                      ·
                        rfl

theorem cell23_2894284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_2894284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894284 prefixEnd_2894284 := by exact prefixLift 2894284
  have htrace : WordTrace (prefixWord ++ tailWord_2894284) baseStart_2894284 baseEnd_2894284 := by
    simpa [prefixWord, tailWord_2894284, baseEnd_2894284] using wordTrace_append hprefix tailTrace_2894284
  have hstable : (prefixWord ++ tailWord_2894284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894284).length < 2 ^ (prefixWord ++ tailWord_2894284).sum := by decide
  have hdescent : baseEnd_2894284 < baseStart_2894284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894316 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 3, 3, 2]
def baseStart_2894316 : Nat := 118140960795 + 2894316 * 2 ^ 59
def prefixEnd_2894316 : Nat := 4983230072969 + 3 ^ 40 * 2894316 * 2
def baseEnd_2894316 : Nat := 1486175273998603209039289

theorem tailTrace_2894316 : CollatzResearch.WordTrace tailWord_2894316 prefixEnd_2894316 1486175273998603209039289 := by
  unfold tailWord_2894316
  simp only [CollatzResearch.WordTrace]
  refine ⟨52782188491197458331947401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70376251321596611109263201 52782188491197458331947401)
  ·
    refine ⟨39586641368398093748960551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52782188491197458331947401 39586641368398093748960551)
    ·
      refine ⟨59379962052597140623440827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39586641368398093748960551 59379962052597140623440827)
      ·
        refine ⟨89069943078895710935161241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59379962052597140623440827 89069943078895710935161241)
        ·
          refine ⟨66802457309171783201370931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89069943078895710935161241 66802457309171783201370931)
          ·
            refine ⟨100203685963757674802056397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66802457309171783201370931 100203685963757674802056397)
            ·
              refine ⟨37576382236409128050771149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100203685963757674802056397 37576382236409128050771149)
              ·
                refine ⟨14091143338653423019039181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37576382236409128050771149 14091143338653423019039181)
                ·
                  refine ⟨5284178751995033632139693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14091143338653423019039181 5284178751995033632139693)
                  ·
                    refine ⟨1981567031998137612052385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5284178751995033632139693 1981567031998137612052385)
                    ·
                      refine ⟨1486175273998603209039289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981567031998137612052385 1486175273998603209039289)
                      ·
                        rfl

theorem cell23_2894316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_2894316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894316 prefixEnd_2894316 := by exact prefixLift 2894316
  have htrace : WordTrace (prefixWord ++ tailWord_2894316) baseStart_2894316 baseEnd_2894316 := by
    simpa [prefixWord, tailWord_2894316, baseEnd_2894316] using wordTrace_append hprefix tailTrace_2894316
  have hstable : (prefixWord ++ tailWord_2894316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894316).length < 2 ^ (prefixWord ++ tailWord_2894316).sum := by decide
  have hdescent : baseEnd_2894316 < baseStart_2894316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894333 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_2894333 : Nat := 118140960795 + 2894333 * 2 ^ 59
def prefixEnd_2894333 : Nat := 4983230072969 + 3 ^ 40 * 2894333 * 2
def baseEnd_2894333 : Nat := 1486184003169729642526711

theorem tailTrace_2894333 : CollatzResearch.WordTrace tailWord_2894333 prefixEnd_2894333 1486184003169729642526711 := by
  unfold tailWord_2894333
  simp only [CollatzResearch.WordTrace]
  refine ⟨105564997023333328567263653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70376664682222219044842435 105564997023333328567263653)
  ·
    refine ⟨19793436941874999106361935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105564997023333328567263653 19793436941874999106361935)
    ·
      refine ⟨29690155412812498659542903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19793436941874999106361935 29690155412812498659542903)
      ·
        refine ⟨44535233119218747989314355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29690155412812498659542903 44535233119218747989314355)
        ·
          refine ⟨66802849678828121983971533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44535233119218747989314355 66802849678828121983971533)
          ·
            refine ⟨25051068629560545743989325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66802849678828121983971533 25051068629560545743989325)
            ·
              refine ⟨9394150736085204653995997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25051068629560545743989325 9394150736085204653995997)
              ·
                refine ⟨3522806526031951745248499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9394150736085204653995997 3522806526031951745248499)
                ·
                  refine ⟨5284209789047927617872749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3522806526031951745248499 5284209789047927617872749)
                  ·
                    refine ⟨1981578670892972856702281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5284209789047927617872749 1981578670892972856702281)
                    ·
                      refine ⟨1486184003169729642526711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981578670892972856702281 1486184003169729642526711)
                      ·
                        rfl

theorem cell23_2894333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_2894333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894333 prefixEnd_2894333 := by exact prefixLift 2894333
  have htrace : WordTrace (prefixWord ++ tailWord_2894333) baseStart_2894333 baseEnd_2894333 := by
    simpa [prefixWord, tailWord_2894333, baseEnd_2894333] using wordTrace_append hprefix tailTrace_2894333
  have hstable : (prefixWord ++ tailWord_2894333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894333).length < 2 ^ (prefixWord ++ tailWord_2894333).sum := by decide
  have hdescent : baseEnd_2894333 < baseStart_2894333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894340 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2894340 : Nat := 118140960795 + 2894340 * 2 ^ 59
def prefixEnd_2894340 : Nat := 4983230072969 + 3 ^ 40 * 2894340 * 2
def baseEnd_2894340 : Nat := 1486187597534311115139179

theorem tailTrace_2894340 : CollatzResearch.WordTrace tailWord_2894340 prefixEnd_2894340 1486187597534311115139179 := by
  unfold tailWord_2894340
  simp only [CollatzResearch.WordTrace]
  refine ⟨52782626167153984381384237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70376834889538645841845649 52782626167153984381384237)
  ·
    refine ⟨19793484812682744143019089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52782626167153984381384237 19793484812682744143019089)
    ·
      refine ⟨14845113609512058107264317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19793484812682744143019089 14845113609512058107264317)
      ·
        refine ⟨5566917603567021790224119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14845113609512058107264317 5566917603567021790224119)
        ·
          refine ⟨8350376405350532685336179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566917603567021790224119 8350376405350532685336179)
          ·
            refine ⟨12525564608025799028004269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8350376405350532685336179 12525564608025799028004269)
            ·
              refine ⟨4697086728009674635501601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12525564608025799028004269 4697086728009674635501601)
              ·
                refine ⟨3522815046007255976626201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697086728009674635501601 3522815046007255976626201)
                ·
                  refine ⟨2642111284505441982469651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3522815046007255976626201 2642111284505441982469651)
                  ·
                    refine ⟨3963166926758162973704477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2642111284505441982469651 3963166926758162973704477)
                    ·
                      refine ⟨1486187597534311115139179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963166926758162973704477 1486187597534311115139179)
                      ·
                        rfl

theorem cell23_2894340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2894340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894340 prefixEnd_2894340 := by exact prefixLift 2894340
  have htrace : WordTrace (prefixWord ++ tailWord_2894340) baseStart_2894340 baseEnd_2894340 := by
    simpa [prefixWord, tailWord_2894340, baseEnd_2894340] using wordTrace_append hprefix tailTrace_2894340
  have hstable : (prefixWord ++ tailWord_2894340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894340).length < 2 ^ (prefixWord ++ tailWord_2894340).sum := by decide
  have hdescent : baseEnd_2894340 < baseStart_2894340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894369 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 7]
def baseStart_2894369 : Nat := 118140960795 + 2894369 * 2 ^ 59
def prefixEnd_2894369 : Nat := 4983230072969 + 3 ^ 40 * 2894369 * 2
def baseEnd_2894369 : Nat := 165133609830365722408505

theorem tailTrace_2894369 : CollatzResearch.WordTrace tailWord_2894369 prefixEnd_2894369 165133609830365722408505 := by
  unfold tailWord_2894369
  simp only [CollatzResearch.WordTrace]
  refine ⟨105566310051202906715574161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70377540034135271143716107 105566310051202906715574161)
  ·
    refine ⟨79174732538402180036680621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105566310051202906715574161 79174732538402180036680621)
    ·
      refine ⟨29690524701900817513755233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79174732538402180036680621 29690524701900817513755233)
      ·
        refine ⟨22267893526425613135316425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29690524701900817513755233 22267893526425613135316425)
        ·
          refine ⟨16700920144819209851487319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22267893526425613135316425 16700920144819209851487319)
          ·
            refine ⟨25051380217228814777230979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16700920144819209851487319 25051380217228814777230979)
            ·
              refine ⟨37577070325843222165846469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25051380217228814777230979 37577070325843222165846469)
              ·
                refine ⟨7045700686095604156096213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37577070325843222165846469 7045700686095604156096213)
                ·
                  refine ⟨165133609830365722408505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7045700686095604156096213 165133609830365722408505)
                  ·
                    rfl

theorem cell23_2894369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_2894369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894369 prefixEnd_2894369 := by exact prefixLift 2894369
  have htrace : WordTrace (prefixWord ++ tailWord_2894369) baseStart_2894369 baseEnd_2894369 := by
    simpa [prefixWord, tailWord_2894369, baseEnd_2894369] using wordTrace_append hprefix tailTrace_2894369
  have hstable : (prefixWord ++ tailWord_2894369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894369).length < 2 ^ (prefixWord ++ tailWord_2894369).sum := by decide
  have hdescent : baseEnd_2894369 < baseStart_2894369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894379 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 3]
def baseStart_2894379 : Nat := 118140960795 + 2894379 * 2 ^ 59
def prefixEnd_2894379 : Nat := 4983230072969 + 3 ^ 40 * 2894379 * 2
def baseEnd_2894379 : Nat := 1486207623279836462551499

theorem tailTrace_2894379 : CollatzResearch.WordTrace tailWord_2894379 prefixEnd_2894379 1486207623279836462551499 := by
  unfold tailWord_2894379
  simp only [CollatzResearch.WordTrace]
  refine ⟨105566674781166678423438191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70377783187444452282292127 105566674781166678423438191)
  ·
    refine ⟨158350012171750017635157287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105566674781166678423438191 158350012171750017635157287)
    ·
      refine ⟨237525018257625026452735931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158350012171750017635157287 237525018257625026452735931)
      ·
        refine ⟨356287527386437539679103897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237525018257625026452735931 356287527386437539679103897)
        ·
          refine ⟨267215645539828154759327923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356287527386437539679103897 267215645539828154759327923)
          ·
            refine ⟨400823468309742232138991885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267215645539828154759327923 400823468309742232138991885)
            ·
              refine ⟨150308800616153337052121957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400823468309742232138991885 150308800616153337052121957)
              ·
                refine ⟨28182900115528750697272867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150308800616153337052121957 28182900115528750697272867)
                ·
                  refine ⟨42274350173293126045909301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28182900115528750697272867 42274350173293126045909301)
                  ·
                    refine ⟨3963220328746230566803997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42274350173293126045909301 3963220328746230566803997)
                    ·
                      refine ⟨1486207623279836462551499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963220328746230566803997 1486207623279836462551499)
                      ·
                        rfl

theorem cell23_2894379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 3].length) (baseStart_2894379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894379 prefixEnd_2894379 := by exact prefixLift 2894379
  have htrace : WordTrace (prefixWord ++ tailWord_2894379) baseStart_2894379 baseEnd_2894379 := by
    simpa [prefixWord, tailWord_2894379, baseEnd_2894379] using wordTrace_append hprefix tailTrace_2894379
  have hstable : (prefixWord ++ tailWord_2894379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894379).length < 2 ^ (prefixWord ++ tailWord_2894379).sum := by decide
  have hdescent : baseEnd_2894379 < baseStart_2894379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894454 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_2894454 : Nat := 118140960795 + 2894454 * 2 ^ 59
def prefixEnd_2894454 : Nat := 4983230072969 + 3 ^ 40 * 2894454 * 2
def baseEnd_2894454 : Nat := 165138459369880407679295

theorem tailTrace_2894454 : CollatzResearch.WordTrace tailWord_2894454 prefixEnd_2894454 165138459369880407679295 := by
  unfold tailWord_2894454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598088140993435389526151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70379606837263310821612277 6598088140993435389526151)
  ·
    refine ⟨9897132211490153084289227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6598088140993435389526151 9897132211490153084289227)
    ·
      refine ⟨14845698317235229626433841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9897132211490153084289227 14845698317235229626433841)
      ·
        refine ⟨11134273737926422219825381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14845698317235229626433841 11134273737926422219825381)
        ·
          refine ⟨2087676325861204166217259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11134273737926422219825381 2087676325861204166217259)
          ·
            refine ⟨3131514488791806249325889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087676325861204166217259 3131514488791806249325889)
            ·
              refine ⟨2348635866593854686994417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131514488791806249325889 2348635866593854686994417)
              ·
                refine ⟨1761476899945391015245813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348635866593854686994417 1761476899945391015245813)
                ·
                  refine ⟨165138459369880407679295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1761476899945391015245813 165138459369880407679295)
                  ·
                    rfl

theorem cell23_2894454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_2894454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894454 prefixEnd_2894454 := by exact prefixLift 2894454
  have htrace : WordTrace (prefixWord ++ tailWord_2894454) baseStart_2894454 baseEnd_2894454 := by
    simpa [prefixWord, tailWord_2894454, baseEnd_2894454] using wordTrace_append hprefix tailTrace_2894454
  have hstable : (prefixWord ++ tailWord_2894454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894454).length < 2 ^ (prefixWord ++ tailWord_2894454).sum := by decide
  have hdescent : baseEnd_2894454 < baseStart_2894454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894479 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_2894479 : Nat := 118140960795 + 2894479 * 2 ^ 59
def prefixEnd_2894479 : Nat := 4983230072969 + 3 ^ 40 * 2894479 * 2
def baseEnd_2894479 : Nat := 1486258971345286071301039

theorem tailTrace_2894479 : CollatzResearch.WordTrace tailWord_2894479 prefixEnd_2894479 1486258971345286071301039 := by
  unfold tailWord_2894479
  simp only [CollatzResearch.WordTrace]
  refine ⟨105570322080804395502078491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70380214720536263668052327 105570322080804395502078491)
  ·
    refine ⟨158355483121206593253117737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105570322080804395502078491 158355483121206593253117737)
    ·
      refine ⟨118766612340904944939838303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158355483121206593253117737 118766612340904944939838303)
      ·
        refine ⟨178149918511357417409757455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118766612340904944939838303 178149918511357417409757455)
        ·
          refine ⟨267224877767036126114636183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178149918511357417409757455 267224877767036126114636183)
          ·
            refine ⟨400837316650554189171954275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267224877767036126114636183 400837316650554189171954275)
            ·
              refine ⟨601255974975831283757931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400837316650554189171954275 601255974975831283757931413)
              ·
                refine ⟨28183873826992091426153035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 601255974975831283757931413 28183873826992091426153035)
                ·
                  refine ⟨42275810740488137139229553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28183873826992091426153035 42275810740488137139229553)
                  ·
                    refine ⟨31706858055366102854422165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42275810740488137139229553 31706858055366102854422165)
                    ·
                      refine ⟨1486258971345286071301039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31706858055366102854422165 1486258971345286071301039)
                      ·
                        rfl

theorem cell23_2894479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_2894479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894479 prefixEnd_2894479 := by exact prefixLift 2894479
  have htrace : WordTrace (prefixWord ++ tailWord_2894479) baseStart_2894479 baseEnd_2894479 := by
    simpa [prefixWord, tailWord_2894479, baseEnd_2894479] using wordTrace_append hprefix tailTrace_2894479
  have hstable : (prefixWord ++ tailWord_2894479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894479).length < 2 ^ (prefixWord ++ tailWord_2894479).sum := by decide
  have hdescent : baseEnd_2894479 < baseStart_2894479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894490 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2894490 : Nat := 118140960795 + 2894490 * 2 ^ 59
def prefixEnd_2894490 : Nat := 4983230072969 + 3 ^ 40 * 2894490 * 2
def baseEnd_2894490 : Nat := 1486264619632485528263489

theorem tailTrace_2894490 : CollatzResearch.WordTrace tailWord_2894490 prefixEnd_2894490 1486264619632485528263489 := by
  unfold tailWord_2894490
  simp only [CollatzResearch.WordTrace]
  refine ⟨26392680820941136095182231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70380482189176362920485949 26392680820941136095182231)
  ·
    refine ⟨39589021231411704142773347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26392680820941136095182231 39589021231411704142773347)
    ·
      refine ⟨59383531847117556214160021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39589021231411704142773347 59383531847117556214160021)
      ·
        refine ⟨2783603055333635447538751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59383531847117556214160021 2783603055333635447538751)
        ·
          refine ⟨4175404583000453171308127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783603055333635447538751 4175404583000453171308127)
          ·
            refine ⟨6263106874500679756962191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175404583000453171308127 6263106874500679756962191)
            ·
              refine ⟨9394660311751019635443287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263106874500679756962191 9394660311751019635443287)
              ·
                refine ⟨14091990467626529453164931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9394660311751019635443287 14091990467626529453164931)
                ·
                  refine ⟨21137985701439794179747397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14091990467626529453164931 21137985701439794179747397)
                  ·
                    refine ⟨3963372319019961408702637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21137985701439794179747397 3963372319019961408702637)
                    ·
                      refine ⟨1486264619632485528263489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963372319019961408702637 1486264619632485528263489)
                      ·
                        rfl

theorem cell23_2894490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2894490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894490 prefixEnd_2894490 := by exact prefixLift 2894490
  have htrace : WordTrace (prefixWord ++ tailWord_2894490) baseStart_2894490 baseEnd_2894490 := by
    simpa [prefixWord, tailWord_2894490, baseEnd_2894490] using wordTrace_append hprefix tailTrace_2894490
  have hstable : (prefixWord ++ tailWord_2894490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894490).length < 2 ^ (prefixWord ++ tailWord_2894490).sum := by decide
  have hdescent : baseEnd_2894490 < baseStart_2894490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894497 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 1, 4]
def baseStart_2894497 : Nat := 118140960795 + 2894497 * 2 ^ 59
def prefixEnd_2894497 : Nat := 4983230072969 + 3 ^ 40 * 2894497 * 2
def baseEnd_2894497 : Nat := 495422737999022333625319

theorem tailTrace_2894497 : CollatzResearch.WordTrace tailWord_2894497 prefixEnd_2894497 495422737999022333625319 := by
  unfold tailWord_2894497
  simp only [CollatzResearch.WordTrace]
  refine ⟨105570978594739184576233745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70380652396492789717489163 105570978594739184576233745)
  ·
    refine ⟨79178233946054388432175309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105570978594739184576233745 79178233946054388432175309)
    ·
      refine ⟨29691837729770395662065741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79178233946054388432175309 29691837729770395662065741)
      ·
        refine ⟨11134439148663898373274653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29691837729770395662065741 11134439148663898373274653)
        ·
          refine ⟨4175414680748961889977995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11134439148663898373274653 4175414680748961889977995)
          ·
            refine ⟨6263122021123442834966993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175414680748961889977995 6263122021123442834966993)
            ·
              refine ⟨4697341515842582126225245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263122021123442834966993 4697341515842582126225245)
              ·
                refine ⟨1761503068440968297334467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4697341515842582126225245 1761503068440968297334467)
                ·
                  refine ⟨2642254602661452446001701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761503068440968297334467 2642254602661452446001701)
                  ·
                    refine ⟨495422737999022333625319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2642254602661452446001701 495422737999022333625319)
                    ·
                      rfl

theorem cell23_2894497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_2894497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894497 prefixEnd_2894497 := by exact prefixLift 2894497
  have htrace : WordTrace (prefixWord ++ tailWord_2894497) baseStart_2894497 baseEnd_2894497 := by
    simpa [prefixWord, tailWord_2894497, baseEnd_2894497] using wordTrace_append hprefix tailTrace_2894497
  have hstable : (prefixWord ++ tailWord_2894497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894497).length < 2 ^ (prefixWord ++ tailWord_2894497).sum := by decide
  have hdescent : baseEnd_2894497 < baseStart_2894497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894510 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_2894510 : Nat := 118140960795 + 2894510 * 2 ^ 59
def prefixEnd_2894510 : Nat := 4983230072969 + 3 ^ 40 * 2894510 * 2
def baseEnd_2894510 : Nat := 165141654360619494445933

theorem tailTrace_2894510 : CollatzResearch.WordTrace tailWord_2894510 prefixEnd_2894510 165141654360619494445933 := by
  unfold tailWord_2894510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196431592961510974557123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70380968495794725197637989 13196431592961510974557123)
  ·
    refine ⟨19794647389442266461835685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13196431592961510974557123 19794647389442266461835685)
    ·
      refine ⟨3711496385520424961594191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19794647389442266461835685 3711496385520424961594191)
      ·
        refine ⟨5567244578280637442391287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711496385520424961594191 5567244578280637442391287)
        ·
          refine ⟨8350866867420956163586931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567244578280637442391287 8350866867420956163586931)
          ·
            refine ⟨12526300301131434245380397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8350866867420956163586931 12526300301131434245380397)
            ·
              refine ⟨4697362612924287842017649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12526300301131434245380397 4697362612924287842017649)
              ·
                refine ⟨3523021959693215881513237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697362612924287842017649 3523021959693215881513237)
                ·
                  refine ⟨165141654360619494445933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3523021959693215881513237 165141654360619494445933)
                  ·
                    rfl

theorem cell23_2894510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_2894510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894510 prefixEnd_2894510 := by exact prefixLift 2894510
  have htrace : WordTrace (prefixWord ++ tailWord_2894510) baseStart_2894510 baseEnd_2894510 := by
    simpa [prefixWord, tailWord_2894510, baseEnd_2894510] using wordTrace_append hprefix tailTrace_2894510
  have hstable : (prefixWord ++ tailWord_2894510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894510).length < 2 ^ (prefixWord ++ tailWord_2894510).sum := by decide
  have hdescent : baseEnd_2894510 < baseStart_2894510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894540 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_2894540 : Nat := 118140960795 + 2894540 * 2 ^ 59
def prefixEnd_2894540 : Nat := 4983230072969 + 3 ^ 40 * 2894540 * 2
def baseEnd_2894540 : Nat := 495430097888403444212753

theorem tailTrace_2894540 : CollatzResearch.WordTrace tailWord_2894540 prefixEnd_2894540 495430097888403444212753 := by
  unfold tailWord_2894540
  simp only [CollatzResearch.WordTrace]
  refine ⟨52786273466791701460024537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70381697955722268613366049 52786273466791701460024537)
  ·
    refine ⟨39589705100093776095018403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52786273466791701460024537 39589705100093776095018403)
    ·
      refine ⟨59384557650140664142527605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39589705100093776095018403 59384557650140664142527605)
      ·
        refine ⟨5567302279700687263361963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59384557650140664142527605 5567302279700687263361963)
        ·
          refine ⟨8350953419551030895042945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567302279700687263361963 8350953419551030895042945)
          ·
            refine ⟨6263215064663273171282209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8350953419551030895042945 6263215064663273171282209)
            ·
              refine ⟨4697411298497454878461657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263215064663273171282209 4697411298497454878461657)
              ·
                refine ⟨3523058473873091158846243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697411298497454878461657 3523058473873091158846243)
                ·
                  refine ⟨5284587710809636738269365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523058473873091158846243 5284587710809636738269365)
                  ·
                    refine ⟨495430097888403444212753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5284587710809636738269365 495430097888403444212753)
                    ·
                      rfl

theorem cell23_2894540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_2894540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894540 prefixEnd_2894540 := by exact prefixLift 2894540
  have htrace : WordTrace (prefixWord ++ tailWord_2894540) baseStart_2894540 baseEnd_2894540 := by
    simpa [prefixWord, tailWord_2894540, baseEnd_2894540] using wordTrace_append hprefix tailTrace_2894540
  have hstable : (prefixWord ++ tailWord_2894540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894540).length < 2 ^ (prefixWord ++ tailWord_2894540).sum := by decide
  have hdescent : baseEnd_2894540 < baseStart_2894540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894563 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2894563 : Nat := 118140960795 + 2894563 * 2 ^ 59
def prefixEnd_2894563 : Nat := 4983230072969 + 3 ^ 40 * 2894563 * 2
def baseEnd_2894563 : Nat := 1486302103720263742650653

theorem tailTrace_2894563 : CollatzResearch.WordTrace tailWord_2894563 prefixEnd_2894563 1486302103720263742650653 := by
  unfold tailWord_2894563
  simp only [CollatzResearch.WordTrace]
  refine ⟨105573385812500077848136343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70382257208333385232090895 105573385812500077848136343)
  ·
    refine ⟨158360078718750116772204515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105573385812500077848136343 158360078718750116772204515)
    ·
      refine ⟨237540118078125175158306773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158360078718750116772204515 237540118078125175158306773)
      ·
        refine ⟨5567346517456058792772815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 237540118078125175158306773 5567346517456058792772815)
        ·
          refine ⟨8351019776184088189159223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567346517456058792772815 8351019776184088189159223)
          ·
            refine ⟨12526529664276132283738835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351019776184088189159223 12526529664276132283738835)
            ·
              refine ⟨18789794496414198425608253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12526529664276132283738835 18789794496414198425608253)
              ·
                refine ⟨7046172936155324409603095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18789794496414198425608253 7046172936155324409603095)
                ·
                  refine ⟨10569259404232986614404643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7046172936155324409603095 10569259404232986614404643)
                  ·
                    refine ⟨15853889106349479921606965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10569259404232986614404643 15853889106349479921606965)
                    ·
                      refine ⟨1486302103720263742650653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15853889106349479921606965 1486302103720263742650653)
                      ·
                        rfl

theorem cell23_2894563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2894563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894563 prefixEnd_2894563 := by exact prefixLift 2894563
  have htrace : WordTrace (prefixWord ++ tailWord_2894563) baseStart_2894563 baseEnd_2894563 := by
    simpa [prefixWord, tailWord_2894563, baseEnd_2894563] using wordTrace_append hprefix tailTrace_2894563
  have hstable : (prefixWord ++ tailWord_2894563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894563).length < 2 ^ (prefixWord ++ tailWord_2894563).sum := by decide
  have hdescent : baseEnd_2894563 < baseStart_2894563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894593 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_2894593 : Nat := 118140960795 + 2894593 * 2 ^ 59
def prefixEnd_2894593 : Nat := 4983230072969 + 3 ^ 40 * 2894593 * 2
def baseEnd_2894593 : Nat := 1486317508139898625275515

theorem tailTrace_2894593 : CollatzResearch.WordTrace tailWord_2894593 prefixEnd_2894593 1486317508139898625275515 := by
  unfold tailWord_2894593
  simp only [CollatzResearch.WordTrace]
  refine ⟨105574480002391392971728433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70382986668260928647818955 105574480002391392971728433)
  ·
    refine ⟨79180860001793544728796325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105574480002391392971728433 79180860001793544728796325)
    ·
      refine ⟨14846411250336289636649311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79180860001793544728796325 14846411250336289636649311)
      ·
        refine ⟨22269616875504434454973967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14846411250336289636649311 22269616875504434454973967)
        ·
          refine ⟨33404425313256651682460951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22269616875504434454973967 33404425313256651682460951)
          ·
            refine ⟨50106637969884977523691427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33404425313256651682460951 50106637969884977523691427)
            ·
              refine ⟨75159956954827466285537141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50106637969884977523691427 75159956954827466285537141)
              ·
                refine ⟨7046245964515074964269107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75159956954827466285537141 7046245964515074964269107)
                ·
                  refine ⟨10569368946772612446403661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7046245964515074964269107 10569368946772612446403661)
                  ·
                    refine ⟨3963513355039729667401373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10569368946772612446403661 3963513355039729667401373)
                    ·
                      refine ⟨1486317508139898625275515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963513355039729667401373 1486317508139898625275515)
                      ·
                        rfl

theorem cell23_2894593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_2894593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894593 prefixEnd_2894593 := by exact prefixLift 2894593
  have htrace : WordTrace (prefixWord ++ tailWord_2894593) baseStart_2894593 baseEnd_2894593 := by
    simpa [prefixWord, tailWord_2894593, baseEnd_2894593] using wordTrace_append hprefix tailTrace_2894593
  have hstable : (prefixWord ++ tailWord_2894593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894593).length < 2 ^ (prefixWord ++ tailWord_2894593).sum := by decide
  have hdescent : baseEnd_2894593 < baseStart_2894593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894628 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_2894628 : Nat := 118140960795 + 2894628 * 2 ^ 59
def prefixEnd_2894628 : Nat := 4983230072969 + 3 ^ 40 * 2894628 * 2
def baseEnd_2894628 : Nat := 1486335479962805988337855

theorem tailTrace_2894628 : CollatzResearch.WordTrace tailWord_2894628 prefixEnd_2894628 1486335479962805988337855 := by
  unfold tailWord_2894628
  simp only [CollatzResearch.WordTrace]
  refine ⟨52787878278632296974626269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70383837704843062632835025 52787878278632296974626269)
  ·
    refine ⟨19795454354487111365484851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52787878278632296974626269 19795454354487111365484851)
    ·
      refine ⟨29693181531730667048227277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19795454354487111365484851 29693181531730667048227277)
      ·
        refine ⟨11134943074399000143085229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29693181531730667048227277 11134943074399000143085229)
        ·
          refine ⟨4175603652899625053656961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11134943074399000143085229 4175603652899625053656961)
          ·
            refine ⟨3131702739674718790242721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4175603652899625053656961 3131702739674718790242721)
            ·
              refine ⟨2348777054756039092682041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131702739674718790242721 2348777054756039092682041)
              ·
                refine ⟨1761582791067029319511531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348777054756039092682041 1761582791067029319511531)
                ·
                  refine ⟨2642374186600543979267297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761582791067029319511531 2642374186600543979267297)
                  ·
                    refine ⟨1981780639950407984450473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642374186600543979267297 1981780639950407984450473)
                    ·
                      refine ⟨1486335479962805988337855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981780639950407984450473 1486335479962805988337855)
                      ·
                        rfl

theorem cell23_2894628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_2894628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894628 prefixEnd_2894628 := by exact prefixLift 2894628
  have htrace : WordTrace (prefixWord ++ tailWord_2894628) baseStart_2894628 baseEnd_2894628 := by
    simpa [prefixWord, tailWord_2894628, baseEnd_2894628] using wordTrace_append hprefix tailTrace_2894628
  have hstable : (prefixWord ++ tailWord_2894628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894628).length < 2 ^ (prefixWord ++ tailWord_2894628).sum := by decide
  have hdescent : baseEnd_2894628 < baseStart_2894628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894643 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 2, 6]
def baseStart_2894643 : Nat := 118140960795 + 2894643 * 2 ^ 59
def prefixEnd_2894643 : Nat := 4983230072969 + 3 ^ 40 * 2894643 * 2
def baseEnd_2894643 : Nat := 495447727390874476550095

theorem tailTrace_2894643 : CollatzResearch.WordTrace tailWord_2894643 prefixEnd_2894643 495447727390874476550095 := by
  unfold tailWord_2894643
  simp only [CollatzResearch.WordTrace]
  refine ⟨105576303652210251511048583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70384202434806834340699055 105576303652210251511048583)
  ·
    refine ⟨158364455478315377266572875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105576303652210251511048583 158364455478315377266572875)
    ·
      refine ⟨237546683217473065899859313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158364455478315377266572875 237546683217473065899859313)
      ·
        refine ⟨178160012413104799424894485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237546683217473065899859313 178160012413104799424894485)
        ·
          refine ⟨8351250581864287473041929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 178160012413104799424894485 8351250581864287473041929)
          ·
            refine ⟨6263437936398215604781447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351250581864287473041929 6263437936398215604781447)
            ·
              refine ⟨9395156904597323407172171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263437936398215604781447 9395156904597323407172171)
              ·
                refine ⟨14092735356895985110758257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395156904597323407172171 14092735356895985110758257)
                ·
                  refine ⟨10569551517671988833068693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14092735356895985110758257 10569551517671988833068693)
                  ·
                    refine ⟨495447727390874476550095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10569551517671988833068693 495447727390874476550095)
                    ·
                      rfl

theorem cell23_2894643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 6].length) (baseStart_2894643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894643 prefixEnd_2894643 := by exact prefixLift 2894643
  have htrace : WordTrace (prefixWord ++ tailWord_2894643) baseStart_2894643 baseEnd_2894643 := by
    simpa [prefixWord, tailWord_2894643, baseEnd_2894643] using wordTrace_append hprefix tailTrace_2894643
  have hstable : (prefixWord ++ tailWord_2894643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894643).length < 2 ^ (prefixWord ++ tailWord_2894643).sum := by decide
  have hdescent : baseEnd_2894643 < baseStart_2894643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894684 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2894684 : Nat := 118140960795 + 2894684 * 2 ^ 59
def prefixEnd_2894684 : Nat := 4983230072969 + 3 ^ 40 * 2894684 * 2
def baseEnd_2894684 : Nat := 1486364234879457769237597

theorem tailTrace_2894684 : CollatzResearch.WordTrace tailWord_2894684 prefixEnd_2894684 1486364234879457769237597 := by
  unfold tailWord_2894684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52788899522530857756645553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70385199363374477008860737 52788899522530857756645553)
  ·
    refine ⟨39591674641898143317484165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52788899522530857756645553 39591674641898143317484165)
    ·
      refine ⟨7423438995355901872028281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39591674641898143317484165 7423438995355901872028281)
      ·
        refine ⟨5567579246516926404021211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7423438995355901872028281 5567579246516926404021211)
        ·
          refine ⟨8351368869775389606031817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567579246516926404021211 8351368869775389606031817)
          ·
            refine ⟨6263526652331542204523863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351368869775389606031817 6263526652331542204523863)
            ·
              refine ⟨9395289978497313306785795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263526652331542204523863 9395289978497313306785795)
              ·
                refine ⟨14092934967745969960178693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395289978497313306785795 14092934967745969960178693)
                ·
                  refine ⟨2642425306452369367533505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14092934967745969960178693 2642425306452369367533505)
                  ·
                    refine ⟨1981818979839277025650129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642425306452369367533505 1981818979839277025650129)
                    ·
                      refine ⟨1486364234879457769237597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981818979839277025650129 1486364234879457769237597)
                      ·
                        rfl

theorem cell23_2894684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2894684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894684 prefixEnd_2894684 := by exact prefixLift 2894684
  have htrace : WordTrace (prefixWord ++ tailWord_2894684) baseStart_2894684 baseEnd_2894684 := by
    simpa [prefixWord, tailWord_2894684, baseEnd_2894684] using wordTrace_append hprefix tailTrace_2894684
  have hstable : (prefixWord ++ tailWord_2894684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894684).length < 2 ^ (prefixWord ++ tailWord_2894684).sum := by decide
  have hdescent : baseEnd_2894684 < baseStart_2894684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894723 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4]
def baseStart_2894723 : Nat := 118140960795 + 2894723 * 2 ^ 59
def prefixEnd_2894723 : Nat := 4983230072969 + 3 ^ 40 * 2894723 * 2
def baseEnd_2894723 : Nat := 1486384260624983116649917

theorem tailTrace_2894723 : CollatzResearch.WordTrace tailWord_2894723 prefixEnd_2894723 1486384260624983116649917 := by
  unfold tailWord_2894723
  simp only [CollatzResearch.WordTrace]
  refine ⟨105579221491920425173960823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70386147661280283449307215 105579221491920425173960823)
  ·
    refine ⟨158368832237880637760941235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105579221491920425173960823 158368832237880637760941235)
    ·
      refine ⟨237553248356820956641411853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158368832237880637760941235 237553248356820956641411853)
      ·
        refine ⟨89082468133807858740529445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237553248356820956641411853 89082468133807858740529445)
        ·
          refine ⟨16702962775088973513849271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89082468133807858740529445 16702962775088973513849271)
          ·
            refine ⟨25054444162633460270773907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16702962775088973513849271 25054444162633460270773907)
            ·
              refine ⟨37581666243950190406160861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25054444162633460270773907 37581666243950190406160861)
              ·
                refine ⟨14093124841481321402310323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37581666243950190406160861 14093124841481321402310323)
                ·
                  refine ⟨21139687262221982103465485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14093124841481321402310323 21139687262221982103465485)
                  ·
                    refine ⟨7927382723333243288799557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21139687262221982103465485 7927382723333243288799557)
                    ·
                      refine ⟨1486384260624983116649917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7927382723333243288799557 1486384260624983116649917)
                      ·
                        rfl

theorem cell23_2894723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_2894723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894723 prefixEnd_2894723 := by exact prefixLift 2894723
  have htrace : WordTrace (prefixWord ++ tailWord_2894723) baseStart_2894723 baseEnd_2894723 := by
    simpa [prefixWord, tailWord_2894723, baseEnd_2894723] using wordTrace_append hprefix tailTrace_2894723
  have hstable : (prefixWord ++ tailWord_2894723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894723).length < 2 ^ (prefixWord ++ tailWord_2894723).sum := by decide
  have hdescent : baseEnd_2894723 < baseStart_2894723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894763 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 6]
def baseStart_2894763 : Nat := 118140960795 + 2894763 * 2 ^ 59
def prefixEnd_2894763 : Nat := 4983230072969 + 3 ^ 40 * 2894763 * 2
def baseEnd_2894763 : Nat := 165156088872351440016637

theorem tailTrace_2894763 : CollatzResearch.WordTrace tailWord_2894763 prefixEnd_2894763 165156088872351440016637 := by
  unfold tailWord_2894763
  simp only [CollatzResearch.WordTrace]
  refine ⟨105580680411775512005416943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70387120274517008003611295 105580680411775512005416943)
  ·
    refine ⟨158371020617663268008125415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105580680411775512005416943 158371020617663268008125415)
    ·
      refine ⟨237556530926494902012188123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158371020617663268008125415 237556530926494902012188123)
      ·
        refine ⟨356334796389742353018282185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237556530926494902012188123 356334796389742353018282185)
        ·
          refine ⟨267251097292306764763711639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356334796389742353018282185 267251097292306764763711639)
          ·
            refine ⟨400876645938460147145567459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267251097292306764763711639 400876645938460147145567459)
            ·
              refine ⟨601314968907690220718351189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400876645938460147145567459 601314968907690220718351189)
              ·
                refine ⟨3523329895943497387021589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 601314968907690220718351189 3523329895943497387021589)
                ·
                  refine ⟨165156088872351440016637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3523329895943497387021589 165156088872351440016637)
                  ·
                    rfl

theorem cell23_2894763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 6].length) (baseStart_2894763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894763 prefixEnd_2894763 := by exact prefixLift 2894763
  have htrace : WordTrace (prefixWord ++ tailWord_2894763) baseStart_2894763 baseEnd_2894763 := by
    simpa [prefixWord, tailWord_2894763, baseEnd_2894763] using wordTrace_append hprefix tailTrace_2894763
  have hstable : (prefixWord ++ tailWord_2894763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894763).length < 2 ^ (prefixWord ++ tailWord_2894763).sum := by decide
  have hdescent : baseEnd_2894763 < baseStart_2894763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894777 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2894777 : Nat := 118140960795 + 2894777 * 2 ^ 59
def prefixEnd_2894777 : Nat := 4983230072969 + 3 ^ 40 * 2894777 * 2
def baseEnd_2894777 : Nat := 1486411988580325905374669

theorem tailTrace_2894777 : CollatzResearch.WordTrace tailWord_2894777 prefixEnd_2894777 1486411988580325905374669 := by
  unfold tailWord_2894777
  simp only [CollatzResearch.WordTrace]
  refine ⟨105581191033724792396426585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70387460689149861597617723 105581191033724792396426585)
  ·
    refine ⟨79185893275293594297319939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105581191033724792396426585 79185893275293594297319939)
    ·
      refine ⟨118778839912940391445979909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79185893275293594297319939 118778839912940391445979909)
      ·
        refine ⟨22271032483676323396121233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118778839912940391445979909 22271032483676323396121233)
        ·
          refine ⟨16703274362757242547090925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22271032483676323396121233 16703274362757242547090925)
          ·
            refine ⟨6263727886033965955159097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16703274362757242547090925 6263727886033965955159097)
            ·
              refine ⟨4697795914525474466369323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263727886033965955159097 4697795914525474466369323)
              ·
                refine ⟨7046693871788211699553985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4697795914525474466369323 7046693871788211699553985)
                ·
                  refine ⟨5285020403841158774665489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7046693871788211699553985 5285020403841158774665489)
                  ·
                    refine ⟨3963765302880869080999117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5285020403841158774665489 3963765302880869080999117)
                    ·
                      refine ⟨1486411988580325905374669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963765302880869080999117 1486411988580325905374669)
                      ·
                        rfl

theorem cell23_2894777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2894777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894777 prefixEnd_2894777 := by exact prefixLift 2894777
  have htrace : WordTrace (prefixWord ++ tailWord_2894777) baseStart_2894777 baseEnd_2894777 := by
    simpa [prefixWord, tailWord_2894777, baseEnd_2894777] using wordTrace_append hprefix tailTrace_2894777
  have hstable : (prefixWord ++ tailWord_2894777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894777).length < 2 ^ (prefixWord ++ tailWord_2894777).sum := by decide
  have hdescent : baseEnd_2894777 < baseStart_2894777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894793 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_2894793 : Nat := 118140960795 + 2894793 * 2 ^ 59
def prefixEnd_2894793 : Nat := 4983230072969 + 3 ^ 40 * 2894793 * 2
def baseEnd_2894793 : Nat := 495473401423599280924865

theorem tailTrace_2894793 : CollatzResearch.WordTrace tailWord_2894793 prefixEnd_2894793 495473401423599280924865 := by
  unfold tailWord_2894793
  simp only [CollatzResearch.WordTrace]
  refine ⟨105581774601666827129009033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70387849734444551419339355 105581774601666827129009033)
  ·
    refine ⟨79186330951250120346756775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105581774601666827129009033 79186330951250120346756775)
    ·
      refine ⟨118779496426875180520135163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79186330951250120346756775 118779496426875180520135163)
      ·
        refine ⟨178169244640312770780202745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118779496426875180520135163 178169244640312770780202745)
        ·
          refine ⟨133626933480234578085152059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178169244640312770780202745 133626933480234578085152059)
          ·
            refine ⟨200440400220351867127728089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133626933480234578085152059 200440400220351867127728089)
            ·
              refine ⟨150330300165263900345796067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200440400220351867127728089 150330300165263900345796067)
              ·
                refine ⟨225495450247895850518694101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150330300165263900345796067 225495450247895850518694101)
                ·
                  refine ⟨5285049615185058996531893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 225495450247895850518694101 5285049615185058996531893)
                  ·
                    refine ⟨495473401423599280924865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5285049615185058996531893 495473401423599280924865)
                    ·
                      rfl

theorem cell23_2894793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_2894793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894793 prefixEnd_2894793 := by exact prefixLift 2894793
  have htrace : WordTrace (prefixWord ++ tailWord_2894793) baseStart_2894793 baseEnd_2894793 := by
    simpa [prefixWord, tailWord_2894793, baseEnd_2894793] using wordTrace_append hprefix tailTrace_2894793
  have hstable : (prefixWord ++ tailWord_2894793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894793).length < 2 ^ (prefixWord ++ tailWord_2894793).sum := by decide
  have hdescent : baseEnd_2894793 < baseStart_2894793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894800 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 3, 5, 2]
def baseStart_2894800 : Nat := 118140960795 + 2894800 * 2 ^ 59
def prefixEnd_2894800 : Nat := 4983230072969 + 3 ^ 40 * 2894800 * 2
def baseEnd_2894800 : Nat := 1486423798635379315387063

theorem tailTrace_2894800 : CollatzResearch.WordTrace tailWord_2894800 prefixEnd_2894800 1486423798635379315387063 := by
  unfold tailWord_2894800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52791014956320733662256927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70388019941760978216342569 52791014956320733662256927)
  ·
    refine ⟨79186522434481100493385391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52791014956320733662256927 79186522434481100493385391)
    ·
      refine ⟨118779783651721650740078087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79186522434481100493385391 118779783651721650740078087)
      ·
        refine ⟨178169675477582476110117131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118779783651721650740078087 178169675477582476110117131)
        ·
          refine ⟨267254513216373714165175697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178169675477582476110117131 267254513216373714165175697)
          ·
            refine ⟨200440884912280285623881773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267254513216373714165175697 200440884912280285623881773)
            ·
              refine ⟨75165331842105107108955665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200440884912280285623881773 75165331842105107108955665)
              ·
                refine ⟨56373998881578830331716749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75165331842105107108955665 56373998881578830331716749)
                ·
                  refine ⟨21140249580592061374393781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56373998881578830331716749 21140249580592061374393781)
                  ·
                    refine ⟨1981898398180505753849417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21140249580592061374393781 1981898398180505753849417)
                    ·
                      refine ⟨1486423798635379315387063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1981898398180505753849417 1486423798635379315387063)
                      ·
                        rfl

theorem cell23_2894800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 5, 2].length) (baseStart_2894800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894800 prefixEnd_2894800 := by exact prefixLift 2894800
  have htrace : WordTrace (prefixWord ++ tailWord_2894800) baseStart_2894800 baseEnd_2894800 := by
    simpa [prefixWord, tailWord_2894800, baseEnd_2894800] using wordTrace_append hprefix tailTrace_2894800
  have hstable : (prefixWord ++ tailWord_2894800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894800).length < 2 ^ (prefixWord ++ tailWord_2894800).sum := by decide
  have hdescent : baseEnd_2894800 < baseStart_2894800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894810 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_2894810 : Nat := 118140960795 + 2894810 * 2 ^ 59
def prefixEnd_2894810 : Nat := 4983230072969 + 3 ^ 40 * 2894810 * 2
def baseEnd_2894810 : Nat := 495476311147308092087339

theorem tailTrace_2894810 : CollatzResearch.WordTrace tailWord_2894810 prefixEnd_2894810 495476311147308092087339 := by
  unfold tailWord_2894810
  simp only [CollatzResearch.WordTrace]
  refine ⟨26395598660651309758094471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70388263095070159354918589 26395598660651309758094471)
  ·
    refine ⟨39593397990976964637141707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26395598660651309758094471 39593397990976964637141707)
    ·
      refine ⟨59390096986465446955712561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39593397990976964637141707 59390096986465446955712561)
      ·
        refine ⟨44542572739849085216784421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59390096986465446955712561 44542572739849085216784421)
        ·
          refine ⟨8351732388721703478147079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44542572739849085216784421 8351732388721703478147079)
          ·
            refine ⟨12527598583082555217220619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351732388721703478147079 12527598583082555217220619)
            ·
              refine ⟨18791397874623832825830929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12527598583082555217220619 18791397874623832825830929)
              ·
                refine ⟨14093548405967874619373197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18791397874623832825830929 14093548405967874619373197)
                ·
                  refine ⟨5285080652237952982264949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14093548405967874619373197 5285080652237952982264949)
                  ·
                    refine ⟨495476311147308092087339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5285080652237952982264949 495476311147308092087339)
                    ·
                      rfl

theorem cell23_2894810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_2894810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894810 prefixEnd_2894810 := by exact prefixLift 2894810
  have htrace : WordTrace (prefixWord ++ tailWord_2894810) baseStart_2894810 baseEnd_2894810 := by
    simpa [prefixWord, tailWord_2894810, baseEnd_2894810] using wordTrace_append hprefix tailTrace_2894810
  have hstable : (prefixWord ++ tailWord_2894810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894810).length < 2 ^ (prefixWord ++ tailWord_2894810).sum := by decide
  have hdescent : baseEnd_2894810 < baseStart_2894810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894840 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 4, 4]
def baseStart_2894840 : Nat := 118140960795 + 2894840 * 2 ^ 59
def prefixEnd_2894840 : Nat := 4983230072969 + 3 ^ 40 * 2894840 * 2
def baseEnd_2894840 : Nat := 495481445953853052962293

theorem tailTrace_2894840 : CollatzResearch.WordTrace tailWord_2894840 prefixEnd_2894840 495481445953853052962293 := by
  unfold tailWord_2894840
  simp only [CollatzResearch.WordTrace]
  refine ⟨52791744416248277077984987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70388992554997702770646649 52791744416248277077984987)
  ·
    refine ⟨79187616624372415616977481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52791744416248277077984987 79187616624372415616977481)
    ·
      refine ⟨59390712468279311712733111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79187616624372415616977481 59390712468279311712733111)
      ·
        refine ⟨89086068702418967569099667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59390712468279311712733111 89086068702418967569099667)
        ·
          refine ⟨133629103053628451353649501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89086068702418967569099667 133629103053628451353649501)
          ·
            refine ⟨50110913645110669257618563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133629103053628451353649501 50110913645110669257618563)
            ·
              refine ⟨75166370467666003886427845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50110913645110669257618563 75166370467666003886427845)
              ·
                refine ⟨14093694462687375728705221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75166370467666003886427845 14093694462687375728705221)
                ·
                  refine ⟨2642567711753882949132229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14093694462687375728705221 2642567711753882949132229)
                  ·
                    refine ⟨495481445953853052962293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2642567711753882949132229 495481445953853052962293)
                    ·
                      rfl

theorem cell23_2894840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_2894840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894840 prefixEnd_2894840 := by exact prefixLift 2894840
  have htrace : WordTrace (prefixWord ++ tailWord_2894840) baseStart_2894840 baseEnd_2894840 := by
    simpa [prefixWord, tailWord_2894840, baseEnd_2894840] using wordTrace_append hprefix tailTrace_2894840
  have hstable : (prefixWord ++ tailWord_2894840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894840).length < 2 ^ (prefixWord ++ tailWord_2894840).sum := by decide
  have hdescent : baseEnd_2894840 < baseStart_2894840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894843 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_2894843 : Nat := 118140960795 + 2894843 * 2 ^ 59
def prefixEnd_2894843 : Nat := 4983230072969 + 3 ^ 40 * 2894843 * 2
def baseEnd_2894843 : Nat := 1486445878303522647149365

theorem tailTrace_2894843 : CollatzResearch.WordTrace tailWord_2894843 prefixEnd_2894843 1486445878303522647149365 := by
  unfold tailWord_2894843
  simp only [CollatzResearch.WordTrace]
  refine ⟨105583598251485685668329183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70389065500990457112219455 105583598251485685668329183)
  ·
    refine ⟨158375397377228528502493775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105583598251485685668329183 158375397377228528502493775)
    ·
      refine ⟨237563096065842792753740663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158375397377228528502493775 237563096065842792753740663)
      ·
        refine ⟨356344644098764189130610995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237563096065842792753740663 356344644098764189130610995)
        ·
          refine ⟨534516966148146283695916493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356344644098764189130610995 534516966148146283695916493)
          ·
            refine ⟨200443862305554856385968685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534516966148146283695916493 200443862305554856385968685)
            ·
              refine ⟨75166448364583071144738257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200443862305554856385968685 75166448364583071144738257)
              ·
                refine ⟨56374836273437303358553693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75166448364583071144738257 56374836273437303358553693)
                ·
                  refine ⟨21140563602538988759457635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56374836273437303358553693 21140563602538988759457635)
                  ·
                    refine ⟨31710845403808483139186453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21140563602538988759457635 31710845403808483139186453)
                    ·
                      refine ⟨1486445878303522647149365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31710845403808483139186453 1486445878303522647149365)
                      ·
                        rfl

theorem cell23_2894843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_2894843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894843 prefixEnd_2894843 := by exact prefixLift 2894843
  have htrace : WordTrace (prefixWord ++ tailWord_2894843) baseStart_2894843 baseEnd_2894843 := by
    simpa [prefixWord, tailWord_2894843, baseEnd_2894843] using wordTrace_append hprefix tailTrace_2894843
  have hstable : (prefixWord ++ tailWord_2894843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894843).length < 2 ^ (prefixWord ++ tailWord_2894843).sum := by decide
  have hdescent : baseEnd_2894843 < baseStart_2894843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894844 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_2894844 : Nat := 118140960795 + 2894844 * 2 ^ 59
def prefixEnd_2894844 : Nat := 4983230072969 + 3 ^ 40 * 2894844 * 2
def baseEnd_2894844 : Nat := 495482130594725714412287

theorem tailTrace_2894844 : CollatzResearch.WordTrace tailWord_2894844 prefixEnd_2894844 495482130594725714412287 := by
  unfold tailWord_2894844
  simp only [CollatzResearch.WordTrace]
  refine ⟨52791817362241031419557793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70389089816321375226077057 52791817362241031419557793)
  ·
    refine ⟨39593863021680773564668345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52791817362241031419557793 39593863021680773564668345)
    ·
      refine ⟨29695397266260580173501259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39593863021680773564668345 29695397266260580173501259)
      ·
        refine ⟨44543095899390870260251889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29695397266260580173501259 44543095899390870260251889)
        ·
          refine ⟨33407321924543152695188917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44543095899390870260251889 33407321924543152695188917)
          ·
            refine ⟨3131936430425920565173961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33407321924543152695188917 3131936430425920565173961)
            ·
              refine ⟨2348952322819440423880471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131936430425920565173961 2348952322819440423880471)
              ·
                refine ⟨3523428484229160635820707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348952322819440423880471 3523428484229160635820707)
                ·
                  refine ⟨5285142726343740953731061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523428484229160635820707 5285142726343740953731061)
                  ·
                    refine ⟨495482130594725714412287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5285142726343740953731061 495482130594725714412287)
                    ·
                      rfl

theorem cell23_2894844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_2894844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894844 prefixEnd_2894844 := by exact prefixLift 2894844
  have htrace : WordTrace (prefixWord ++ tailWord_2894844) baseStart_2894844 baseEnd_2894844 := by
    simpa [prefixWord, tailWord_2894844, baseEnd_2894844] using wordTrace_append hprefix tailTrace_2894844
  have hstable : (prefixWord ++ tailWord_2894844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894844).length < 2 ^ (prefixWord ++ tailWord_2894844).sum := by decide
  have hdescent : baseEnd_2894844 < baseStart_2894844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894853 : List Nat := [1, 3, 1, 1, 2, 3, 12]
def baseStart_2894853 : Nat := 118140960795 + 2894853 * 2 ^ 59
def prefixEnd_2894853 : Nat := 4983230072969 + 3 ^ 40 * 2894853 * 2
def baseEnd_2894853 : Nat := 18351247075432933432399

theorem tailTrace_2894853 : CollatzResearch.WordTrace tailWord_2894853 prefixEnd_2894853 18351247075432933432399 := by
  unfold tailWord_2894853
  simp only [CollatzResearch.WordTrace]
  refine ⟨105583962981449457376193213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70389308654299638250795475 105583962981449457376193213)
  ·
    refine ⟨39593986118043546516072455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105583962981449457376193213 39593986118043546516072455)
    ·
      refine ⟨59390979177065319774108683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39593986118043546516072455 59390979177065319774108683)
      ·
        refine ⟨89086468765597979661163025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59390979177065319774108683 89086468765597979661163025)
        ·
          refine ⟨66814851574198484745872269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89086468765597979661163025 66814851574198484745872269)
          ·
            refine ⟨25055569340324431779702101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66814851574198484745872269 25055569340324431779702101)
            ·
              refine ⟨18351247075432933432399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25055569340324431779702101 18351247075432933432399)
              ·
                rfl

theorem cell23_2894853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 12].length) (baseStart_2894853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894853 prefixEnd_2894853 := by exact prefixLift 2894853
  have htrace : WordTrace (prefixWord ++ tailWord_2894853) baseStart_2894853 baseEnd_2894853 := by
    simpa [prefixWord, tailWord_2894853, baseEnd_2894853] using wordTrace_append hprefix tailTrace_2894853
  have hstable : (prefixWord ++ tailWord_2894853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894853).length < 2 ^ (prefixWord ++ tailWord_2894853).sum := by decide
  have hdescent : baseEnd_2894853 < baseStart_2894853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894874 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_2894874 : Nat := 118140960795 + 2894874 * 2 ^ 59
def prefixEnd_2894874 : Nat := 4983230072969 + 3 ^ 40 * 2894874 * 2
def baseEnd_2894874 : Nat := 495487265401270675287241

theorem tailTrace_2894874 : CollatzResearch.WordTrace tailWord_2894874 prefixEnd_2894874 495487265401270675287241 := by
  unfold tailWord_2894874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396182228593344490676919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70389819276248918641805117 26396182228593344490676919)
  ·
    refine ⟨39594273342890016736015379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26396182228593344490676919 39594273342890016736015379)
    ·
      refine ⟨59391410014335025104023069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39594273342890016736015379 59391410014335025104023069)
      ·
        refine ⟨22271778755375634414008651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59391410014335025104023069 22271778755375634414008651)
        ·
          refine ⟨33407668133063451621012977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22271778755375634414008651 33407668133063451621012977)
          ·
            refine ⟨25055751099797588715759733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33407668133063451621012977 25055751099797588715759733)
            ·
              refine ⟨2348976665606023942102475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25055751099797588715759733 2348976665606023942102475)
              ·
                refine ⟨3523464998409035913153713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348976665606023942102475 3523464998409035913153713)
                ·
                  refine ⟨2642598748806776934865285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3523464998409035913153713 2642598748806776934865285)
                  ·
                    refine ⟨495487265401270675287241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2642598748806776934865285 495487265401270675287241)
                    ·
                      rfl

theorem cell23_2894874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_2894874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894874 prefixEnd_2894874 := by exact prefixLift 2894874
  have htrace : WordTrace (prefixWord ++ tailWord_2894874) baseStart_2894874 baseEnd_2894874 := by
    simpa [prefixWord, tailWord_2894874, baseEnd_2894874] using wordTrace_append hprefix tailTrace_2894874
  have hstable : (prefixWord ++ tailWord_2894874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894874).length < 2 ^ (prefixWord ++ tailWord_2894874).sum := by decide
  have hdescent : baseEnd_2894874 < baseStart_2894874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894877 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2894877 : Nat := 118140960795 + 2894877 * 2 ^ 59
def prefixEnd_2894877 : Nat := 4983230072969 + 3 ^ 40 * 2894877 * 2
def baseEnd_2894877 : Nat := 1486463336645775514124209

theorem tailTrace_2894877 : CollatzResearch.WordTrace tailWord_2894877 prefixEnd_2894877 1486463336645775514124209 := by
  unfold tailWord_2894877
  simp only [CollatzResearch.WordTrace]
  refine ⟨105584838333362509475066885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70389892222241672983377923 105584838333362509475066885)
  ·
    refine ⟨19797157187505470526575041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105584838333362509475066885 19797157187505470526575041)
    ·
      refine ⟨14847867890629102894931281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19797157187505470526575041 14847867890629102894931281)
      ·
        refine ⟨11135900917971827171198461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14847867890629102894931281 11135900917971827171198461)
        ·
          refine ⟨4175962844239435189199423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11135900917971827171198461 4175962844239435189199423)
          ·
            refine ⟨6263944266359152783799135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175962844239435189199423 6263944266359152783799135)
            ·
              refine ⟨9395916399538729175698703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263944266359152783799135 9395916399538729175698703)
              ·
                refine ⟨14093874599308093763548055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9395916399538729175698703 14093874599308093763548055)
                ·
                  refine ⟨21140811898962140645322083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14093874599308093763548055 21140811898962140645322083)
                  ·
                    refine ⟨31711217848443210967983125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21140811898962140645322083 31711217848443210967983125)
                    ·
                      refine ⟨1486463336645775514124209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31711217848443210967983125 1486463336645775514124209)
                      ·
                        rfl

theorem cell23_2894877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2894877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894877 prefixEnd_2894877 := by exact prefixLift 2894877
  have htrace : WordTrace (prefixWord ++ tailWord_2894877) baseStart_2894877 baseEnd_2894877 := by
    simpa [prefixWord, tailWord_2894877, baseEnd_2894877] using wordTrace_append hprefix tailTrace_2894877
  have hstable : (prefixWord ++ tailWord_2894877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894877).length < 2 ^ (prefixWord ++ tailWord_2894877).sum := by decide
  have hdescent : baseEnd_2894877 < baseStart_2894877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894884 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2894884 : Nat := 118140960795 + 2894884 * 2 ^ 59
def prefixEnd_2894884 : Nat := 4983230072969 + 3 ^ 40 * 2894884 * 2
def baseEnd_2894884 : Nat := 1486466931010356986736677

theorem tailTrace_2894884 : CollatzResearch.WordTrace tailWord_2894884 prefixEnd_2894884 1486466931010356986736677 := by
  unfold tailWord_2894884
  simp only [CollatzResearch.WordTrace]
  refine ⟨52792546822168574835285853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70390062429558099780381137 52792546822168574835285853)
  ·
    refine ⟨19797205058313215563232195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52792546822168574835285853 19797205058313215563232195)
    ·
      refine ⟨29695807587469823344848293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19797205058313215563232195 29695807587469823344848293)
      ·
        refine ⟨5567963922650591877159055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29695807587469823344848293 5567963922650591877159055)
        ·
          refine ⟨8351945883975887815738583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567963922650591877159055 8351945883975887815738583)
          ·
            refine ⟨12527918825963831723607875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351945883975887815738583 12527918825963831723607875)
            ·
              refine ⟨18791878238945747585411813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12527918825963831723607875 18791878238945747585411813)
              ·
                refine ⟨3523477169802327672264715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18791878238945747585411813 3523477169802327672264715)
                ·
                  refine ⟨5285215754703491508397073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523477169802327672264715 5285215754703491508397073)
                  ·
                    refine ⟨3963911816027618631297805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5285215754703491508397073 3963911816027618631297805)
                    ·
                      refine ⟨1486466931010356986736677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963911816027618631297805 1486466931010356986736677)
                      ·
                        rfl

theorem cell23_2894884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2894884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894884 prefixEnd_2894884 := by exact prefixLift 2894884
  have htrace : WordTrace (prefixWord ++ tailWord_2894884) baseStart_2894884 baseEnd_2894884 := by
    simpa [prefixWord, tailWord_2894884, baseEnd_2894884] using wordTrace_append hprefix tailTrace_2894884
  have hstable : (prefixWord ++ tailWord_2894884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894884).length < 2 ^ (prefixWord ++ tailWord_2894884).sum := by decide
  have hdescent : baseEnd_2894884 < baseStart_2894884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894887 : List Nat := [1, 1, 7, 1, 1, 2, 1, 9]
def baseStart_2894887 : Nat := 118140960795 + 2894887 * 2 ^ 59
def prefixEnd_2894887 : Nat := 4983230072969 + 3 ^ 40 * 2894887 * 2
def baseEnd_2894887 : Nat := 55054387831567424999969

theorem tailTrace_2894887 : CollatzResearch.WordTrace tailWord_2894887 prefixEnd_2894887 55054387831567424999969 := by
  unfold tailWord_2894887
  simp only [CollatzResearch.WordTrace]
  refine ⟨105585203063326281182930915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70390135375550854121953943 105585203063326281182930915)
  ·
    refine ⟨158377804594989421774396373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105585203063326281182930915 158377804594989421774396373)
    ·
      refine ⟨3711979795195064572837415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158377804594989421774396373 3711979795195064572837415)
      ·
        refine ⟨5567969692792596859256123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711979795195064572837415 5567969692792596859256123)
        ·
          refine ⟨8351954539188895288884185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567969692792596859256123 8351954539188895288884185)
          ·
            refine ⟨6263965904391671466663139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351954539188895288884185 6263965904391671466663139)
            ·
              refine ⟨9395948856587507199994709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6263965904391671466663139 9395948856587507199994709)
              ·
                refine ⟨55054387831567424999969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9395948856587507199994709 55054387831567424999969)
                ·
                  rfl

theorem cell23_2894887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 9].length) (baseStart_2894887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894887 prefixEnd_2894887 := by exact prefixLift 2894887
  have htrace : WordTrace (prefixWord ++ tailWord_2894887) baseStart_2894887 baseEnd_2894887 := by
    simpa [prefixWord, tailWord_2894887, baseEnd_2894887] using wordTrace_append hprefix tailTrace_2894887
  have hstable : (prefixWord ++ tailWord_2894887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894887).length < 2 ^ (prefixWord ++ tailWord_2894887).sum := by decide
  have hdescent : baseEnd_2894887 < baseStart_2894887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894897 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2894897 : Nat := 118140960795 + 2894897 * 2 ^ 59
def prefixEnd_2894897 : Nat := 4983230072969 + 3 ^ 40 * 2894897 * 2
def baseEnd_2894897 : Nat := 1486473606258865435874117

theorem tailTrace_2894897 : CollatzResearch.WordTrace tailWord_2894897 prefixEnd_2894897 1486473606258865435874117 := by
  unfold tailWord_2894897
  simp only [CollatzResearch.WordTrace]
  refine ⟨105585567793290052890794945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70390378528860035260529963 105585567793290052890794945)
  ·
    refine ⟨79189175844967539668096209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105585567793290052890794945 79189175844967539668096209)
    ·
      refine ⟨59391881883725654751072157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79189175844967539668096209 59391881883725654751072157)
      ·
        refine ⟨22271955706397120531652059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59391881883725654751072157 22271955706397120531652059)
        ·
          refine ⟨33407933559595680797478089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22271955706397120531652059 33407933559595680797478089)
          ·
            refine ⟨25055950169696760598108567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33407933559595680797478089 25055950169696760598108567)
            ·
              refine ⟨37583925254545140897162851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25055950169696760598108567 37583925254545140897162851)
              ·
                refine ⟨56375887881817711345744277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37583925254545140897162851 56375887881817711345744277)
                ·
                  refine ⟨2642619744460205219331763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56375887881817711345744277 2642619744460205219331763)
                  ·
                    refine ⟨3963929616690307828997645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2642619744460205219331763 3963929616690307828997645)
                    ·
                      refine ⟨1486473606258865435874117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3963929616690307828997645 1486473606258865435874117)
                      ·
                        rfl

theorem cell23_2894897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2894897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894897 prefixEnd_2894897 := by exact prefixLift 2894897
  have htrace : WordTrace (prefixWord ++ tailWord_2894897) baseStart_2894897 baseEnd_2894897 := by
    simpa [prefixWord, tailWord_2894897, baseEnd_2894897] using wordTrace_append hprefix tailTrace_2894897
  have hstable : (prefixWord ++ tailWord_2894897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894897).length < 2 ^ (prefixWord ++ tailWord_2894897).sum := by decide
  have hdescent : baseEnd_2894897 < baseStart_2894897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894920 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2894920 : Nat := 118140960795 + 2894920 * 2 ^ 59
def prefixEnd_2894920 : Nat := 4983230072969 + 3 ^ 40 * 2894920 * 2
def baseEnd_2894920 : Nat := 1486485416313918845886511

theorem tailTrace_2894920 : CollatzResearch.WordTrace tailWord_2894920 prefixEnd_2894920 1486485416313918845886511 := by
  unfold tailWord_2894920
  simp only [CollatzResearch.WordTrace]
  refine ⟨52793203336103363909441107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70390937781471151879254809 52793203336103363909441107)
  ·
    refine ⟨79189805004155045864161661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52793203336103363909441107 79189805004155045864161661)
    ·
      refine ⟨29696176876558142199060623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79189805004155045864161661 29696176876558142199060623)
      ·
        refine ⟨44544265314837213298590935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29696176876558142199060623 44544265314837213298590935)
        ·
          refine ⟨66816397972255819947886403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44544265314837213298590935 66816397972255819947886403)
          ·
            refine ⟨100224596958383729921829605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66816397972255819947886403 100224596958383729921829605)
            ·
              refine ⟨18792111929696949360343051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100224596958383729921829605 18792111929696949360343051)
              ·
                refine ⟨28188167894545424040514577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18792111929696949360343051 28188167894545424040514577)
                ·
                  refine ⟨21141125920909068030385933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28188167894545424040514577 21141125920909068030385933)
                  ·
                    refine ⟨7927922220340900511394725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21141125920909068030385933 7927922220340900511394725)
                    ·
                      refine ⟨1486485416313918845886511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7927922220340900511394725 1486485416313918845886511)
                      ·
                        rfl

theorem cell23_2894920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2894920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894920 prefixEnd_2894920 := by exact prefixLift 2894920
  have htrace : WordTrace (prefixWord ++ tailWord_2894920) baseStart_2894920 baseEnd_2894920 := by
    simpa [prefixWord, tailWord_2894920, baseEnd_2894920] using wordTrace_append hprefix tailTrace_2894920
  have hstable : (prefixWord ++ tailWord_2894920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894920).length < 2 ^ (prefixWord ++ tailWord_2894920).sum := by decide
  have hdescent : baseEnd_2894920 < baseStart_2894920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894954 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_2894954 : Nat := 118140960795 + 2894954 * 2 ^ 59
def prefixEnd_2894954 : Nat := 4983230072969 + 3 ^ 40 * 2894954 * 2
def baseEnd_2894954 : Nat := 1486502874656171712861355

theorem tailTrace_2894954 : CollatzResearch.WordTrace tailWord_2894954 prefixEnd_2894954 1486502874656171712861355 := by
  unfold tailWord_2894954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396911688520887906404979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70391764502722367750413277 26396911688520887906404979)
  ·
    refine ⟨39595367532781331859607469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26396911688520887906404979 39595367532781331859607469)
    ·
      refine ⟨14848262824792999447352801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39595367532781331859607469 14848262824792999447352801)
      ·
        refine ⟨11136197118594749585514601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14848262824792999447352801 11136197118594749585514601)
        ·
          refine ⟨8352147838946062189135951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11136197118594749585514601 8352147838946062189135951)
          ·
            refine ⟨12528221758419093283703927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8352147838946062189135951 12528221758419093283703927)
            ·
              refine ⟨18792332637628639925555891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12528221758419093283703927 18792332637628639925555891)
              ·
                refine ⟨28188498956442959888333837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18792332637628639925555891 28188498956442959888333837)
                ·
                  refine ⟨10570687108666109958125189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28188498956442959888333837 10570687108666109958125189)
                  ·
                    refine ⟨1982003832874895617148473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10570687108666109958125189 1982003832874895617148473)
                    ·
                      refine ⟨1486502874656171712861355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982003832874895617148473 1486502874656171712861355)
                      ·
                        rfl

theorem cell23_2894954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_2894954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894954 prefixEnd_2894954 := by exact prefixLift 2894954
  have htrace : WordTrace (prefixWord ++ tailWord_2894954) baseStart_2894954 baseEnd_2894954 := by
    simpa [prefixWord, tailWord_2894954, baseEnd_2894954] using wordTrace_append hprefix tailTrace_2894954
  have hstable : (prefixWord ++ tailWord_2894954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894954).length < 2 ^ (prefixWord ++ tailWord_2894954).sum := by decide
  have hdescent : baseEnd_2894954 < baseStart_2894954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894957 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2894957 : Nat := 118140960795 + 2894957 * 2 ^ 59
def prefixEnd_2894957 : Nat := 4983230072969 + 3 ^ 40 * 2894957 * 2
def baseEnd_2894957 : Nat := 1486504415098135201123841

theorem tailTrace_2894957 : CollatzResearch.WordTrace tailWord_2894957 prefixEnd_2894957 1486504415098135201123841 := by
  unfold tailWord_2894957
  simp only [CollatzResearch.WordTrace]
  refine ⟨105587756173072683137979125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70391837448715122091986083 105587756173072683137979125)
  ·
    refine ⟨9898852141225564044185543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105587756173072683137979125 9898852141225564044185543)
    ·
      refine ⟨14848278211838346066278315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9898852141225564044185543 14848278211838346066278315)
      ·
        refine ⟨22272417317757519099417473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14848278211838346066278315 22272417317757519099417473)
        ·
          refine ⟨16704312988318139324563105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22272417317757519099417473 16704312988318139324563105)
          ·
            refine ⟨12528234741238604493422329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16704312988318139324563105 12528234741238604493422329)
            ·
              refine ⟨9396176055928953370066747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12528234741238604493422329 9396176055928953370066747)
              ·
                refine ⟨14094264083893430055100121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396176055928953370066747 14094264083893430055100121)
                ·
                  refine ⟨10570698062920072541325091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14094264083893430055100121 10570698062920072541325091)
                  ·
                    refine ⟨15856047094380108811987637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10570698062920072541325091 15856047094380108811987637)
                    ·
                      refine ⟨1486504415098135201123841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15856047094380108811987637 1486504415098135201123841)
                      ·
                        rfl

theorem cell23_2894957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2894957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894957 prefixEnd_2894957 := by exact prefixLift 2894957
  have htrace : WordTrace (prefixWord ++ tailWord_2894957) baseStart_2894957 baseEnd_2894957 := by
    simpa [prefixWord, tailWord_2894957, baseEnd_2894957] using wordTrace_append hprefix tailTrace_2894957
  have hstable : (prefixWord ++ tailWord_2894957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894957).length < 2 ^ (prefixWord ++ tailWord_2894957).sum := by decide
  have hdescent : baseEnd_2894957 < baseStart_2894957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894958 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2894958 : Nat := 118140960795 + 2894958 * 2 ^ 59
def prefixEnd_2894958 : Nat := 4983230072969 + 3 ^ 40 * 2894958 * 2
def baseEnd_2894958 : Nat := 1486504928578789697211337

theorem tailTrace_2894958 : CollatzResearch.WordTrace tailWord_2894958 prefixEnd_2894958 1486504928578789697211337 := by
  unfold tailWord_2894958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13198474080758632538595691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70391861764046040205843685 13198474080758632538595691)
  ·
    refine ⟨19797711121137948807893537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13198474080758632538595691 19797711121137948807893537)
    ·
      refine ⟨14848283340853461605920153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19797711121137948807893537 14848283340853461605920153)
      ·
        refine ⟨11136212505640096204440115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14848283340853461605920153 11136212505640096204440115)
        ·
          refine ⟨16704318758460144306660173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11136212505640096204440115 16704318758460144306660173)
          ·
            refine ⟨6264119534422554114997565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16704318758460144306660173 6264119534422554114997565)
            ·
              refine ⟨2349044825408457793124087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6264119534422554114997565 2349044825408457793124087)
              ·
                refine ⟨3523567238112686689686131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349044825408457793124087 3523567238112686689686131)
                ·
                  refine ⟨5285350857169030034529197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523567238112686689686131 5285350857169030034529197)
                  ·
                    refine ⟨1982006571438386262948449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5285350857169030034529197 1982006571438386262948449)
                    ·
                      refine ⟨1486504928578789697211337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982006571438386262948449 1486504928578789697211337)
                      ·
                        rfl

theorem cell23_2894958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2894958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894958 prefixEnd_2894958 := by exact prefixLift 2894958
  have htrace : WordTrace (prefixWord ++ tailWord_2894958) baseStart_2894958 baseEnd_2894958 := by
    simpa [prefixWord, tailWord_2894958, baseEnd_2894958] using wordTrace_append hprefix tailTrace_2894958
  have hstable : (prefixWord ++ tailWord_2894958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894958).length < 2 ^ (prefixWord ++ tailWord_2894958).sum := by decide
  have hdescent : baseEnd_2894958 < baseStart_2894958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2894984 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2894984 : Nat := 118140960795 + 2894984 * 2 ^ 59
def prefixEnd_2894984 : Nat := 4983230072969 + 3 ^ 40 * 2894984 * 2
def baseEnd_2894984 : Nat := 1486518279075806595486217

theorem tailTrace_2894984 : CollatzResearch.WordTrace tailWord_2894984 prefixEnd_2894984 1486518279075806595486217 := by
  unfold tailWord_2894984
  simp only [CollatzResearch.WordTrace]
  refine ⟨52794370471987433374606003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70392493962649911166141337 52794370471987433374606003)
  ·
    refine ⟨79191555707981150061909005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52794370471987433374606003 79191555707981150061909005)
    ·
      refine ⟨29696833390492931273215877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79191555707981150061909005 29696833390492931273215877)
      ·
        refine ⟨5568156260717424613727977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29696833390492931273215877 5568156260717424613727977)
        ·
          refine ⟨4176117195538068460295983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5568156260717424613727977 4176117195538068460295983)
          ·
            refine ⟨6264175793307102690443975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176117195538068460295983 6264175793307102690443975)
            ·
              refine ⟨9396263689960654035665963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264175793307102690443975 9396263689960654035665963)
              ·
                refine ⟨14094395534940981053498945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396263689960654035665963 14094395534940981053498945)
                ·
                  refine ⟨10570796651205735790124209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14094395534940981053498945 10570796651205735790124209)
                  ·
                    refine ⟨7928097488404301842593157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10570796651205735790124209 7928097488404301842593157)
                    ·
                      refine ⟨1486518279075806595486217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7928097488404301842593157 1486518279075806595486217)
                      ·
                        rfl

theorem cell23_2894984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2894984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2894984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2894984 prefixEnd_2894984 := by exact prefixLift 2894984
  have htrace : WordTrace (prefixWord ++ tailWord_2894984) baseStart_2894984 baseEnd_2894984 := by
    simpa [prefixWord, tailWord_2894984, baseEnd_2894984] using wordTrace_append hprefix tailTrace_2894984
  have hstable : (prefixWord ++ tailWord_2894984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2894984).length < 2 ^ (prefixWord ++ tailWord_2894984).sum := by decide
  have hdescent : baseEnd_2894984 < baseStart_2894984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2894984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895027 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 4]
def baseStart_2895027 : Nat := 118140960795 + 2895027 * 2 ^ 59
def prefixEnd_2895027 : Nat := 4983230072969 + 3 ^ 40 * 2895027 * 2
def baseEnd_2895027 : Nat := 1486540358743949927248519

theorem tailTrace_2895027 : CollatzResearch.WordTrace tailWord_2895027 prefixEnd_2895027 1486540358743949927248519 := by
  unfold tailWord_2895027
  simp only [CollatzResearch.WordTrace]
  refine ⟨105590309282819085093027335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70393539521879390062018223 105590309282819085093027335)
  ·
    refine ⟨158385463924228627639541003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105590309282819085093027335 158385463924228627639541003)
    ·
      refine ⟨237578195886342941459311505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158385463924228627639541003 237578195886342941459311505)
      ·
        refine ⟨178183646914757206094483629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237578195886342941459311505 178183646914757206094483629)
        ·
          refine ⟨66818867593033952285431361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178183646914757206094483629 66818867593033952285431361)
          ·
            refine ⟨50114150694775464214073521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66818867593033952285431361 50114150694775464214073521)
            ·
              refine ⟨37585613021081598160555141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50114150694775464214073521 37585613021081598160555141)
              ·
                refine ⟨7047302441452799655104089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37585613021081598160555141 7047302441452799655104089)
                ·
                  refine ⟨5285476831089599741328067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7047302441452799655104089 5285476831089599741328067)
                  ·
                    refine ⟨7928215246634399611992101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5285476831089599741328067 7928215246634399611992101)
                    ·
                      refine ⟨1486540358743949927248519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7928215246634399611992101 1486540358743949927248519)
                      ·
                        rfl

theorem cell23_2895027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_2895027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895027 prefixEnd_2895027 := by exact prefixLift 2895027
  have htrace : WordTrace (prefixWord ++ tailWord_2895027) baseStart_2895027 baseEnd_2895027 := by
    simpa [prefixWord, tailWord_2895027, baseEnd_2895027] using wordTrace_append hprefix tailTrace_2895027
  have hstable : (prefixWord ++ tailWord_2895027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895027).length < 2 ^ (prefixWord ++ tailWord_2895027).sum := by decide
  have hdescent : baseEnd_2895027 < baseStart_2895027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895071 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 1, 4]
def baseStart_2895071 : Nat := 118140960795 + 2895071 * 2 ^ 59
def prefixEnd_2895071 : Nat := 4983230072969 + 3 ^ 40 * 2895071 * 2
def baseEnd_2895071 : Nat := 495520983964249251699439

theorem tailTrace_2895071 : CollatzResearch.WordTrace tailWord_2895071 prefixEnd_2895071 495520983964249251699439 := by
  unfold tailWord_2895071
  simp only [CollatzResearch.WordTrace]
  refine ⟨105591914094659680607629067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70394609396439787071752711 105591914094659680607629067)
  ·
    refine ⟨158387871141989520911443601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105591914094659680607629067 158387871141989520911443601)
    ·
      refine ⟨118790903356492140683582701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158387871141989520911443601 118790903356492140683582701)
      ·
        refine ⟨44546588758684552756343513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118790903356492140683582701 44546588758684552756343513)
        ·
          refine ⟨33409941569013414567257635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44546588758684552756343513 33409941569013414567257635)
          ·
            refine ⟨50114912353520121850886453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33409941569013414567257635 50114912353520121850886453)
            ·
              refine ⟨4698273033142511423520605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50114912353520121850886453 4698273033142511423520605)
              ·
                refine ⟨1761852387428441783820227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4698273033142511423520605 1761852387428441783820227)
                ·
                  refine ⟨2642778581142662675730341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761852387428441783820227 2642778581142662675730341)
                  ·
                    refine ⟨495520983964249251699439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2642778581142662675730341 495520983964249251699439)
                    ·
                      rfl

theorem cell23_2895071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 4].length) (baseStart_2895071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895071 prefixEnd_2895071 := by exact prefixLift 2895071
  have htrace : WordTrace (prefixWord ++ tailWord_2895071) baseStart_2895071 baseEnd_2895071 := by
    simpa [prefixWord, tailWord_2895071, baseEnd_2895071] using wordTrace_append hprefix tailTrace_2895071
  have hstable : (prefixWord ++ tailWord_2895071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895071).length < 2 ^ (prefixWord ++ tailWord_2895071).sum := by decide
  have hdescent : baseEnd_2895071 < baseStart_2895071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895097 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_2895097 : Nat := 118140960795 + 2895097 * 2 ^ 59
def prefixEnd_2895097 : Nat := 4983230072969 + 3 ^ 40 * 2895097 * 2
def baseEnd_2895097 : Nat := 495525434129921551124399

theorem tailTrace_2895097 : CollatzResearch.WordTrace tailWord_2895097 prefixEnd_2895097 495525434129921551124399 := by
  unfold tailWord_2895097
  simp only [CollatzResearch.WordTrace]
  refine ⟨105592862392565487048075545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70395241595043658032050363 105592862392565487048075545)
  ·
    refine ⟨79194646794424115286056659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105592862392565487048075545 79194646794424115286056659)
    ·
      refine ⟨118791970191636172929084989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79194646794424115286056659 118791970191636172929084989)
      ·
        refine ⟨44546988821863564848406871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118791970191636172929084989 44546988821863564848406871)
        ·
          refine ⟨66820483232795347272610307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44546988821863564848406871 66820483232795347272610307)
          ·
            refine ⟨100230724849193020908915461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66820483232795347272610307 100230724849193020908915461)
            ·
              refine ⟨18793260909223691420421649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100230724849193020908915461 18793260909223691420421649)
              ·
                refine ⟨14094945681917768565316237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18793260909223691420421649 14094945681917768565316237)
                ·
                  refine ⟨5285604630719163211993589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14094945681917768565316237 5285604630719163211993589)
                  ·
                    refine ⟨495525434129921551124399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5285604630719163211993589 495525434129921551124399)
                    ·
                      rfl

theorem cell23_2895097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_2895097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895097 prefixEnd_2895097 := by exact prefixLift 2895097
  have htrace : WordTrace (prefixWord ++ tailWord_2895097) baseStart_2895097 baseEnd_2895097 := by
    simpa [prefixWord, tailWord_2895097, baseEnd_2895097] using wordTrace_append hprefix tailTrace_2895097
  have hstable : (prefixWord ++ tailWord_2895097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895097).length < 2 ^ (prefixWord ++ tailWord_2895097).sum := by decide
  have hdescent : baseEnd_2895097 < baseStart_2895097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895104 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 6, 3, 2]
def baseStart_2895104 : Nat := 118140960795 + 2895104 * 2 ^ 59
def prefixEnd_2895104 : Nat := 4983230072969 + 3 ^ 40 * 2895104 * 2
def baseEnd_2895104 : Nat := 1486579896754346125985665

theorem tailTrace_2895104 : CollatzResearch.WordTrace tailWord_2895104 prefixEnd_2895104 1486579896754346125985665 := by
  unfold tailWord_2895104
  simp only [CollatzResearch.WordTrace]
  refine ⟨52796558851770063621790183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70395411802360084829053577 52796558851770063621790183)
  ·
    refine ⟨79194838277655095432685275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52796558851770063621790183 79194838277655095432685275)
    ·
      refine ⟨118792257416482643149027913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79194838277655095432685275 118792257416482643149027913)
      ·
        refine ⟨89094193062361982361770935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118792257416482643149027913 89094193062361982361770935)
        ·
          refine ⟨133641289593542973542656403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89094193062361982361770935 133641289593542973542656403)
          ·
            refine ⟨200461934390314460313984605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133641289593542973542656403 200461934390314460313984605)
            ·
              refine ⟨75173225396367922617744227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200461934390314460313984605 75173225396367922617744227)
              ·
                refine ⟨112759838094551883926616341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75173225396367922617744227 112759838094551883926616341)
                ·
                  refine ⟨5285617410682119559060141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112759838094551883926616341 5285617410682119559060141)
                  ·
                    refine ⟨1982106529005794834647553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5285617410682119559060141 1982106529005794834647553)
                    ·
                      refine ⟨1486579896754346125985665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982106529005794834647553 1486579896754346125985665)
                      ·
                        rfl

theorem cell23_2895104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_2895104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895104 prefixEnd_2895104 := by exact prefixLift 2895104
  have htrace : WordTrace (prefixWord ++ tailWord_2895104) baseStart_2895104 baseEnd_2895104 := by
    simpa [prefixWord, tailWord_2895104, baseEnd_2895104] using wordTrace_append hprefix tailTrace_2895104
  have hstable : (prefixWord ++ tailWord_2895104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895104).length < 2 ^ (prefixWord ++ tailWord_2895104).sum := by decide
  have hdescent : baseEnd_2895104 < baseStart_2895104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895121 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 2, 3, 2]
def baseStart_2895121 : Nat := 118140960795 + 2895121 * 2 ^ 59
def prefixEnd_2895121 : Nat := 4983230072969 + 3 ^ 40 * 2895121 * 2
def baseEnd_2895121 : Nat := 1486588625925472559473087

theorem tailTrace_2895121 : CollatzResearch.WordTrace tailWord_2895121 prefixEnd_2895121 1486588625925472559473087 := by
  unfold tailWord_2895121
  simp only [CollatzResearch.WordTrace]
  refine ⟨105593737744478539146949217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70395825162985692764632811 105593737744478539146949217)
  ·
    refine ⟨79195303308358904360211913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105593737744478539146949217 79195303308358904360211913)
    ·
      refine ⟨59396477481269178270158935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79195303308358904360211913 59396477481269178270158935)
      ·
        refine ⟨89094716221903767405238403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59396477481269178270158935 89094716221903767405238403)
        ·
          refine ⟨133642074332855651107857605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89094716221903767405238403 133642074332855651107857605)
          ·
            refine ⟨25057888937410434582723301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133642074332855651107857605 25057888937410434582723301)
            ·
              refine ⟨4698354175764456484260619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25057888937410434582723301 4698354175764456484260619)
              ·
                refine ⟨7047531263646684726390929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698354175764456484260619 7047531263646684726390929)
                ·
                  refine ⟨5285648447735013544793197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7047531263646684726390929 5285648447735013544793197)
                  ·
                    refine ⟨1982118167900630079297449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5285648447735013544793197 1982118167900630079297449)
                    ·
                      refine ⟨1486588625925472559473087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982118167900630079297449 1486588625925472559473087)
                      ·
                        rfl

theorem cell23_2895121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_2895121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895121 prefixEnd_2895121 := by exact prefixLift 2895121
  have htrace : WordTrace (prefixWord ++ tailWord_2895121) baseStart_2895121 baseEnd_2895121 := by
    simpa [prefixWord, tailWord_2895121, baseEnd_2895121] using wordTrace_append hprefix tailTrace_2895121
  have hstable : (prefixWord ++ tailWord_2895121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895121).length < 2 ^ (prefixWord ++ tailWord_2895121).sum := by decide
  have hdescent : baseEnd_2895121 < baseStart_2895121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895151 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 3, 2, 2]
def baseStart_2895151 : Nat := 118140960795 + 2895151 * 2 ^ 59
def prefixEnd_2895151 : Nat := 4983230072969 + 3 ^ 40 * 2895151 * 2
def baseEnd_2895151 : Nat := 1486604030345107442097949

theorem tailTrace_2895151 : CollatzResearch.WordTrace tailWord_2895151 prefixEnd_2895151 1486604030345107442097949 := by
  unfold tailWord_2895151
  simp only [CollatzResearch.WordTrace]
  refine ⟨105594831934369854270541307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70396554622913236180360871 105594831934369854270541307)
  ·
    refine ⟨158392247901554781405811961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105594831934369854270541307 158392247901554781405811961)
    ·
      refine ⟨118794185926166086054358971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158392247901554781405811961 118794185926166086054358971)
      ·
        refine ⟨178191278889249129081538457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118794185926166086054358971 178191278889249129081538457)
        ·
          refine ⟨133643459166936846811153843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178191278889249129081538457 133643459166936846811153843)
          ·
            refine ⟨200465188750405270216730765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133643459166936846811153843 200465188750405270216730765)
            ·
              refine ⟨75174445781401976331274037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200465188750405270216730765 75174445781401976331274037)
              ·
                refine ⟨7047604292006435281056941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75174445781401976331274037 7047604292006435281056941)
                ·
                  refine ⟨2642851609502413230396353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7047604292006435281056941 2642851609502413230396353)
                  ·
                    refine ⟨1982138707126809922797265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642851609502413230396353 1982138707126809922797265)
                    ·
                      refine ⟨1486604030345107442097949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982138707126809922797265 1486604030345107442097949)
                      ·
                        rfl

theorem cell23_2895151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 2, 2].length) (baseStart_2895151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895151 prefixEnd_2895151 := by exact prefixLift 2895151
  have htrace : WordTrace (prefixWord ++ tailWord_2895151) baseStart_2895151 baseEnd_2895151 := by
    simpa [prefixWord, tailWord_2895151, baseEnd_2895151] using wordTrace_append hprefix tailTrace_2895151
  have hstable : (prefixWord ++ tailWord_2895151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895151).length < 2 ^ (prefixWord ++ tailWord_2895151).sum := by decide
  have hdescent : baseEnd_2895151 < baseStart_2895151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895161 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 1, 6]
def baseStart_2895161 : Nat := 118140960795 + 2895161 * 2 ^ 59
def prefixEnd_2895161 : Nat := 4983230072969 + 3 ^ 40 * 2895161 * 2
def baseEnd_2895161 : Nat := 495536388383884134324301

theorem tailTrace_2895161 : CollatzResearch.WordTrace tailWord_2895161 prefixEnd_2895161 495536388383884134324301 := by
  unfold tailWord_2895161
  simp only [CollatzResearch.WordTrace]
  refine ⟨105595196664333625978405337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70396797776222417318936891 105595196664333625978405337)
  ·
    refine ⟨79196397498250219483804003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105595196664333625978405337 79196397498250219483804003)
    ·
      refine ⟨118794596247375329225706005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79196397498250219483804003 118794596247375329225706005)
      ·
        refine ⟨5568496699095718557454969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118794596247375329225706005 5568496699095718557454969)
        ·
          refine ⟨4176372524321788918091227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5568496699095718557454969 4176372524321788918091227)
          ·
            refine ⟨6264558786482683377136841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176372524321788918091227 6264558786482683377136841)
            ·
              refine ⟨4698419089862012532852631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6264558786482683377136841 4698419089862012532852631)
              ·
                refine ⟨7047628634793018799278947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4698419089862012532852631 7047628634793018799278947)
                ·
                  refine ⟨10571442952189528198918421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047628634793018799278947 10571442952189528198918421)
                  ·
                    refine ⟨495536388383884134324301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10571442952189528198918421 495536388383884134324301)
                    ·
                      rfl

theorem cell23_2895161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_2895161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895161 prefixEnd_2895161 := by exact prefixLift 2895161
  have htrace : WordTrace (prefixWord ++ tailWord_2895161) baseStart_2895161 baseEnd_2895161 := by
    simpa [prefixWord, tailWord_2895161, baseEnd_2895161] using wordTrace_append hprefix tailTrace_2895161
  have hstable : (prefixWord ++ tailWord_2895161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895161).length < 2 ^ (prefixWord ++ tailWord_2895161).sum := by decide
  have hdescent : baseEnd_2895161 < baseStart_2895161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895164 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2895164 : Nat := 118140960795 + 2895164 * 2 ^ 59
def prefixEnd_2895164 : Nat := 4983230072969 + 3 ^ 40 * 2895164 * 2
def baseEnd_2895164 : Nat := 1486610705593615891235389

theorem tailTrace_2895164 : CollatzResearch.WordTrace tailWord_2895164 prefixEnd_2895164 1486610705593615891235389 := by
  unfold tailWord_2895164
  simp only [CollatzResearch.WordTrace]
  refine ⟨52797653041661378745382273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70396870722215171660509697 52797653041661378745382273)
  ·
    refine ⟨39598239781246034059036705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52797653041661378745382273 39598239781246034059036705)
    ·
      refine ⟨29698679835934525544277529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39598239781246034059036705 29698679835934525544277529)
      ·
        refine ⟨22274009876950894158208147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29698679835934525544277529 22274009876950894158208147)
        ·
          refine ⟨33411014815426341237312221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22274009876950894158208147 33411014815426341237312221)
          ·
            refine ⟨12529130555784877963992083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33411014815426341237312221 12529130555784877963992083)
            ·
              refine ⟨18793695833677316945988125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12529130555784877963992083 18793695833677316945988125)
              ·
                refine ⟨7047635937628993854745547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18793695833677316945988125 7047635937628993854745547)
                ·
                  refine ⟨10571453906443490782118321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047635937628993854745547 10571453906443490782118321)
                  ·
                    refine ⟨7928590429832618086588741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10571453906443490782118321 7928590429832618086588741)
                    ·
                      refine ⟨1486610705593615891235389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7928590429832618086588741 1486610705593615891235389)
                      ·
                        rfl

theorem cell23_2895164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2895164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895164 prefixEnd_2895164 := by exact prefixLift 2895164
  have htrace : WordTrace (prefixWord ++ tailWord_2895164) baseStart_2895164 baseEnd_2895164 := by
    simpa [prefixWord, tailWord_2895164, baseEnd_2895164] using wordTrace_append hprefix tailTrace_2895164
  have hstable : (prefixWord ++ tailWord_2895164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895164).length < 2 ^ (prefixWord ++ tailWord_2895164).sum := by decide
  have hdescent : baseEnd_2895164 < baseStart_2895164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895184 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_2895184 : Nat := 118140960795 + 2895184 * 2 ^ 59
def prefixEnd_2895184 : Nat := 4983230072969 + 3 ^ 40 * 2895184 * 2
def baseEnd_2895184 : Nat := 1486620975206705812985297

theorem tailTrace_2895184 : CollatzResearch.WordTrace tailWord_2895184 prefixEnd_2895184 1486620975206705812985297 := by
  unfold tailWord_2895184
  simp only [CollatzResearch.WordTrace]
  refine ⟨52798017771625150453246303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70397357028833533937661737 52798017771625150453246303)
  ·
    refine ⟨79197026657437725679869455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52798017771625150453246303 79197026657437725679869455)
    ·
      refine ⟨118795539986156588519804183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79197026657437725679869455 118795539986156588519804183)
      ·
        refine ⟨178193309979234882779706275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118795539986156588519804183 178193309979234882779706275)
        ·
          refine ⟨267289964968852324169559413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178193309979234882779706275 267289964968852324169559413)
          ·
            refine ⟨25058434215829905390896195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 267289964968852324169559413 25058434215829905390896195)
            ·
              refine ⟨37587651323744858086344293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25058434215829905390896195 37587651323744858086344293)
              ·
                refine ⟨7047684623202160891189555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37587651323744858086344293 7047684623202160891189555)
                ·
                  refine ⟨10571526934803241336784333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7047684623202160891189555 10571526934803241336784333)
                  ·
                    refine ⟨3964322600551215501294125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10571526934803241336784333 3964322600551215501294125)
                    ·
                      refine ⟨1486620975206705812985297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3964322600551215501294125 1486620975206705812985297)
                      ·
                        rfl

theorem cell23_2895184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_2895184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895184 prefixEnd_2895184 := by exact prefixLift 2895184
  have htrace : WordTrace (prefixWord ++ tailWord_2895184) baseStart_2895184 baseEnd_2895184 := by
    simpa [prefixWord, tailWord_2895184, baseEnd_2895184] using wordTrace_append hprefix tailTrace_2895184
  have hstable : (prefixWord ++ tailWord_2895184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895184).length < 2 ^ (prefixWord ++ tailWord_2895184).sum := by decide
  have hdescent : baseEnd_2895184 < baseStart_2895184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895185 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 1, 2, 2]
def baseStart_2895185 : Nat := 118140960795 + 2895185 * 2 ^ 59
def prefixEnd_2895185 : Nat := 4983230072969 + 3 ^ 40 * 2895185 * 2
def baseEnd_2895185 : Nat := 1486621488687360309072793

theorem tailTrace_2895185 : CollatzResearch.WordTrace tailWord_2895185 prefixEnd_2895185 1486621488687360309072793 := by
  unfold tailWord_2895185
  simp only [CollatzResearch.WordTrace]
  refine ⟨105596072016246678077279009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70397381344164452051519339 105596072016246678077279009)
  ·
    refine ⟨79197054012185008557959257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105596072016246678077279009 79197054012185008557959257)
    ·
      refine ⟨59397790509138756418469443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79197054012185008557959257 59397790509138756418469443)
      ·
        refine ⟨89096685763708134627704165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59397790509138756418469443 89096685763708134627704165)
        ·
          refine ⟨16705628580695275242694531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89096685763708134627704165 16705628580695275242694531)
          ·
            refine ⟨25058442871042912864041797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16705628580695275242694531 25058442871042912864041797)
            ·
              refine ⟨4698458038320546162007837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25058442871042912864041797 4698458038320546162007837)
              ·
                refine ⟨1761921764370204810752939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4698458038320546162007837 1761921764370204810752939)
                ·
                  refine ⟨2642882646555307216129409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761921764370204810752939 2642882646555307216129409)
                  ·
                    refine ⟨1982161984916480412097057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642882646555307216129409 1982161984916480412097057)
                    ·
                      refine ⟨1486621488687360309072793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982161984916480412097057 1486621488687360309072793)
                      ·
                        rfl

theorem cell23_2895185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_2895185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895185 prefixEnd_2895185 := by exact prefixLift 2895185
  have htrace : WordTrace (prefixWord ++ tailWord_2895185) baseStart_2895185 baseEnd_2895185 := by
    simpa [prefixWord, tailWord_2895185, baseEnd_2895185] using wordTrace_append hprefix tailTrace_2895185
  have hstable : (prefixWord ++ tailWord_2895185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895185).length < 2 ^ (prefixWord ++ tailWord_2895185).sum := by decide
  have hdescent : baseEnd_2895185 < baseStart_2895185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895228 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_2895228 : Nat := 118140960795 + 2895228 * 2 ^ 59
def prefixEnd_2895228 : Nat := 4983230072969 + 3 ^ 40 * 2895228 * 2
def baseEnd_2895228 : Nat := 1486643568355503640835095

theorem tailTrace_2895228 : CollatzResearch.WordTrace tailWord_2895228 prefixEnd_2895228 1486643568355503640835095 := by
  unfold tailWord_2895228
  simp only [CollatzResearch.WordTrace]
  refine ⟨52798820177545448210547169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70398426903393930947396225 52798820177545448210547169)
  ·
    refine ⟨39599115133159086157910377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52798820177545448210547169 39599115133159086157910377)
    ·
      refine ⟨29699336349869314618432783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39599115133159086157910377 29699336349869314618432783)
      ·
        refine ⟨44549004524803971927649175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29699336349869314618432783 44549004524803971927649175)
        ·
          refine ⟨66823506787205957891473763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44549004524803971927649175 66823506787205957891473763)
          ·
            refine ⟨100235260180808936837210645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66823506787205957891473763 100235260180808936837210645)
            ·
              refine ⟨4698527820975418914244249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100235260180808936837210645 4698527820975418914244249)
              ·
                refine ⟨3523895865731564185683187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698527820975418914244249 3523895865731564185683187)
                ·
                  refine ⟨5285843798597346278524781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3523895865731564185683187 5285843798597346278524781)
                  ·
                    refine ⟨1982191424474004854446793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5285843798597346278524781 1982191424474004854446793)
                    ·
                      refine ⟨1486643568355503640835095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982191424474004854446793 1486643568355503640835095)
                      ·
                        rfl

theorem cell23_2895228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_2895228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895228 prefixEnd_2895228 := by exact prefixLift 2895228
  have htrace : WordTrace (prefixWord ++ tailWord_2895228) baseStart_2895228 baseEnd_2895228 := by
    simpa [prefixWord, tailWord_2895228, baseEnd_2895228] using wordTrace_append hprefix tailTrace_2895228
  have hstable : (prefixWord ++ tailWord_2895228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895228).length < 2 ^ (prefixWord ++ tailWord_2895228).sum := by decide
  have hdescent : baseEnd_2895228 < baseStart_2895228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895244 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2895244 : Nat := 118140960795 + 2895244 * 2 ^ 59
def prefixEnd_2895244 : Nat := 4983230072969 + 3 ^ 40 * 2895244 * 2
def baseEnd_2895244 : Nat := 1486651784045975578235021

theorem tailTrace_2895244 : CollatzResearch.WordTrace tailWord_2895244 prefixEnd_2895244 1486651784045975578235021 := by
  unfold tailWord_2895244
  simp only [CollatzResearch.WordTrace]
  refine ⟨52799111961516465576838393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70398815948688620769117857 52799111961516465576838393)
  ·
    refine ⟨39599333971137349182628795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52799111961516465576838393 39599333971137349182628795)
    ·
      refine ⟨59399000956706023773943193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39599333971137349182628795 59399000956706023773943193)
      ·
        refine ⟨44549250717529517830457395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59399000956706023773943193 44549250717529517830457395)
        ·
          refine ⟨66823876076294276745686093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44549250717529517830457395 66823876076294276745686093)
          ·
            refine ⟨25058953528610353779632285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66823876076294276745686093 25058953528610353779632285)
            ·
              refine ⟨9397107573228882667362107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25058953528610353779632285 9397107573228882667362107)
              ·
                refine ⟨14095661359843324001043161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397107573228882667362107 14095661359843324001043161)
                ·
                  refine ⟨10571746019882493000782371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14095661359843324001043161 10571746019882493000782371)
                  ·
                    refine ⟨15857619029823739501173557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10571746019882493000782371 15857619029823739501173557)
                    ·
                      refine ⟨1486651784045975578235021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15857619029823739501173557 1486651784045975578235021)
                      ·
                        rfl

theorem cell23_2895244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2895244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895244 prefixEnd_2895244 := by exact prefixLift 2895244
  have htrace : WordTrace (prefixWord ++ tailWord_2895244) baseStart_2895244 baseEnd_2895244 := by
    simpa [prefixWord, tailWord_2895244, baseEnd_2895244] using wordTrace_append hprefix tailTrace_2895244
  have hstable : (prefixWord ++ tailWord_2895244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895244).length < 2 ^ (prefixWord ++ tailWord_2895244).sum := by decide
  have hdescent : baseEnd_2895244 < baseStart_2895244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895258 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2]
def baseStart_2895258 : Nat := 118140960795 + 2895258 * 2 ^ 59
def prefixEnd_2895258 : Nat := 4983230072969 + 3 ^ 40 * 2895258 * 2
def baseEnd_2895258 : Nat := 1486658972775138523459957

theorem tailTrace_2895258 : CollatzResearch.WordTrace tailWord_2895258 prefixEnd_2895258 1486658972775138523459957 := by
  unfold tailWord_2895258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26399683636245552886171607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70399156363321474363124285 26399683636245552886171607)
  ·
    refine ⟨39599525454368329329257411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26399683636245552886171607 39599525454368329329257411)
    ·
      refine ⟨59399288181552493993886117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39599525454368329329257411 59399288181552493993886117)
      ·
        refine ⟨11137366534041092623853647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59399288181552493993886117 11137366534041092623853647)
        ·
          refine ⟨16706049801061638935780471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11137366534041092623853647 16706049801061638935780471)
          ·
            refine ⟨25059074701592458403670707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16706049801061638935780471 25059074701592458403670707)
            ·
              refine ⟨37588612052388687605506061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25059074701592458403670707 37588612052388687605506061)
              ·
                refine ⟨14095729519645757852064773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37588612052388687605506061 14095729519645757852064773)
                ·
                  refine ⟨2642949284933579597262145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14095729519645757852064773 2642949284933579597262145)
                  ·
                    refine ⟨1982211963700184697946609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2642949284933579597262145 1982211963700184697946609)
                    ·
                      refine ⟨1486658972775138523459957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982211963700184697946609 1486658972775138523459957)
                      ·
                        rfl

theorem cell23_2895258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_2895258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895258 prefixEnd_2895258 := by exact prefixLift 2895258
  have htrace : WordTrace (prefixWord ++ tailWord_2895258) baseStart_2895258 baseEnd_2895258 := by
    simpa [prefixWord, tailWord_2895258, baseEnd_2895258] using wordTrace_append hprefix tailTrace_2895258
  have hstable : (prefixWord ++ tailWord_2895258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895258).length < 2 ^ (prefixWord ++ tailWord_2895258).sum := by decide
  have hdescent : baseEnd_2895258 < baseStart_2895258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895304 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2895304 : Nat := 118140960795 + 2895304 * 2 ^ 59
def prefixEnd_2895304 : Nat := 4983230072969 + 3 ^ 40 * 2895304 * 2
def baseEnd_2895304 : Nat := 1486682592885245343484745

theorem tailTrace_2895304 : CollatzResearch.WordTrace tailWord_2895304 prefixEnd_2895304 1486682592885245343484745 := by
  unfold tailWord_2895304
  simp only [CollatzResearch.WordTrace]
  refine ⟨52800206151407780700430483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70400274868543707600573977 52800206151407780700430483)
  ·
    refine ⟨79200309227111671050645725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52800206151407780700430483 79200309227111671050645725)
    ·
      refine ⟨29700115960166876643992147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79200309227111671050645725 29700115960166876643992147)
      ·
        refine ⟨44550173940250314965988221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29700115960166876643992147 44550173940250314965988221)
        ·
          refine ⟨16706315227593868112245583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44550173940250314965988221 16706315227593868112245583)
          ·
            refine ⟨25059472841390802168368375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16706315227593868112245583 25059472841390802168368375)
            ·
              refine ⟨37589209262086203252552563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25059472841390802168368375 37589209262086203252552563)
              ·
                refine ⟨56383813893129304878828845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37589209262086203252552563 56383813893129304878828845)
                ·
                  refine ⟨21143930209923489329560817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56383813893129304878828845 21143930209923489329560817)
                  ·
                    refine ⟨15857947657442616997170613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21143930209923489329560817 15857947657442616997170613)
                    ·
                      refine ⟨1486682592885245343484745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15857947657442616997170613 1486682592885245343484745)
                      ·
                        rfl

theorem cell23_2895304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2895304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895304 prefixEnd_2895304 := by exact prefixLift 2895304
  have htrace : WordTrace (prefixWord ++ tailWord_2895304) baseStart_2895304 baseEnd_2895304 := by
    simpa [prefixWord, tailWord_2895304, baseEnd_2895304] using wordTrace_append hprefix tailTrace_2895304
  have hstable : (prefixWord ++ tailWord_2895304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895304).length < 2 ^ (prefixWord ++ tailWord_2895304).sum := by decide
  have hdescent : baseEnd_2895304 < baseStart_2895304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895351 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_2895351 : Nat := 118140960795 + 2895351 * 2 ^ 59
def prefixEnd_2895351 : Nat := 4983230072969 + 3 ^ 40 * 2895351 * 2
def baseEnd_2895351 : Nat := 1486706726476006659597029

theorem tailTrace_2895351 : CollatzResearch.WordTrace tailWord_2895351 prefixEnd_2895351 1486706726476006659597029 := by
  unfold tailWord_2895351
  simp only [CollatzResearch.WordTrace]
  refine ⟨105602126533645288427821907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70401417689096858951881271 105602126533645288427821907)
  ·
    refine ⟨158403189800467932641732861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105602126533645288427821907 158403189800467932641732861)
    ·
      refine ⟨59401196175175474740649823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158403189800467932641732861 59401196175175474740649823)
      ·
        refine ⟨89101794262763212110974735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59401196175175474740649823 89101794262763212110974735)
        ·
          refine ⟨133652691394144818166462103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89101794262763212110974735 133652691394144818166462103)
          ·
            refine ⟨200479037091217227249693155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133652691394144818166462103 200479037091217227249693155)
            ·
              refine ⟨300718555636825840874539733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200479037091217227249693155 300718555636825840874539733)
              ·
                refine ⟨7048091147738105645497025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 300718555636825840874539733 7048091147738105645497025)
                ·
                  refine ⟨5286068360803579234122769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048091147738105645497025 5286068360803579234122769)
                  ·
                    refine ⟨3964551270602684425592077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286068360803579234122769 3964551270602684425592077)
                    ·
                      refine ⟨1486706726476006659597029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3964551270602684425592077 1486706726476006659597029)
                      ·
                        rfl

theorem cell23_2895351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_2895351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895351 prefixEnd_2895351 := by exact prefixLift 2895351
  have htrace : WordTrace (prefixWord ++ tailWord_2895351) baseStart_2895351 baseEnd_2895351 := by
    simpa [prefixWord, tailWord_2895351, baseEnd_2895351] using wordTrace_append hprefix tailTrace_2895351
  have hstable : (prefixWord ++ tailWord_2895351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895351).length < 2 ^ (prefixWord ++ tailWord_2895351).sum := by decide
  have hdescent : baseEnd_2895351 < baseStart_2895351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895354 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 8]
def baseStart_2895354 : Nat := 118140960795 + 2895354 * 2 ^ 59
def prefixEnd_2895354 : Nat := 4983230072969 + 3 ^ 40 * 2895354 * 2
def baseEnd_2895354 : Nat := 165189807435330016428835

theorem tailTrace_2895354 : CollatzResearch.WordTrace tailWord_2895354 prefixEnd_2895354 165189807435330016428835 := by
  unfold tailWord_2895354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26400558988158604985045279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70401490635089613293454077 26400558988158604985045279)
  ·
    refine ⟨39600838482237907477567919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26400558988158604985045279 39600838482237907477567919)
    ·
      refine ⟨59401257723356861216351879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39600838482237907477567919 59401257723356861216351879)
      ·
        refine ⟨89101886585035291824527819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59401257723356861216351879 89101886585035291824527819)
        ·
          refine ⟨133652829877552937736791729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89101886585035291824527819 133652829877552937736791729)
          ·
            refine ⟨100239622408164703302593797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133652829877552937736791729 100239622408164703302593797)
            ·
              refine ⟨18794929201530881869236337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100239622408164703302593797 18794929201530881869236337)
              ·
                refine ⟨14096196901148161401927253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18794929201530881869236337 14096196901148161401927253)
                ·
                  refine ⟨165189807435330016428835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14096196901148161401927253 165189807435330016428835)
                  ·
                    rfl

theorem cell23_2895354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_2895354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895354 prefixEnd_2895354 := by exact prefixLift 2895354
  have htrace : WordTrace (prefixWord ++ tailWord_2895354) baseStart_2895354 baseEnd_2895354 := by
    simpa [prefixWord, tailWord_2895354, baseEnd_2895354] using wordTrace_append hprefix tailTrace_2895354
  have hstable : (prefixWord ++ tailWord_2895354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895354).length < 2 ^ (prefixWord ++ tailWord_2895354).sum := by decide
  have hdescent : baseEnd_2895354 < baseStart_2895354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895371 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 8]
def baseStart_2895371 : Nat := 118140960795 + 2895371 * 2 ^ 59
def prefixEnd_2895371 : Nat := 4983230072969 + 3 ^ 40 * 2895371 * 2
def baseEnd_2895371 : Nat := 165190777343232953482993

theorem tailTrace_2895371 : CollatzResearch.WordTrace tailWord_2895371 prefixEnd_2895371 165190777343232953482993 := by
  unfold tailWord_2895371
  simp only [CollatzResearch.WordTrace]
  refine ⟨105602855993572831843549967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70401903995715221229033311 105602855993572831843549967)
  ·
    refine ⟨158404283990359247765324951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105602855993572831843549967 158404283990359247765324951)
    ·
      refine ⟨237606425985538871647987427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158404283990359247765324951 237606425985538871647987427)
      ·
        refine ⟨356409638978308307471981141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237606425985538871647987427 356409638978308307471981141)
        ·
          refine ⟨4176675456777050478187279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 356409638978308307471981141 4176675456777050478187279)
          ·
            refine ⟨6265013185165575717280919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176675456777050478187279 6265013185165575717280919)
            ·
              refine ⟨9397519777748363575921379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265013185165575717280919 9397519777748363575921379)
              ·
                refine ⟨14096279666622545363882069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9397519777748363575921379 14096279666622545363882069)
                ·
                  refine ⟨165190777343232953482993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14096279666622545363882069 165190777343232953482993)
                  ·
                    rfl

theorem cell23_2895371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 8].length) (baseStart_2895371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895371 prefixEnd_2895371 := by exact prefixLift 2895371
  have htrace : WordTrace (prefixWord ++ tailWord_2895371) baseStart_2895371 baseEnd_2895371 := by
    simpa [prefixWord, tailWord_2895371, baseEnd_2895371] using wordTrace_append hprefix tailTrace_2895371
  have hstable : (prefixWord ++ tailWord_2895371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895371).length < 2 ^ (prefixWord ++ tailWord_2895371).sum := by decide
  have hdescent : baseEnd_2895371 < baseStart_2895371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895388 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 6]
def baseStart_2895388 : Nat := 118140960795 + 2895388 * 2 ^ 59
def prefixEnd_2895388 : Nat := 4983230072969 + 3 ^ 40 * 2895388 * 2
def baseEnd_2895388 : Nat := 165191747251135890537151

theorem tailTrace_2895388 : CollatzResearch.WordTrace tailWord_2895388 prefixEnd_2895388 165191747251135890537151 := by
  unfold tailWord_2895388
  simp only [CollatzResearch.WordTrace]
  refine ⟨52801738017255621873459409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70402317356340829164612545 52801738017255621873459409)
  ·
    refine ⟨39601303512941716405094557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52801738017255621873459409 39601303512941716405094557)
    ·
      refine ⟨14850488817353143651910459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39601303512941716405094557 14850488817353143651910459)
      ·
        refine ⟨22275733226029715477865689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14850488817353143651910459 22275733226029715477865689)
        ·
          refine ⟨16706799919522286608399267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22275733226029715477865689 16706799919522286608399267)
          ·
            refine ⟨25060199879283429912598901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16706799919522286608399267 25060199879283429912598901)
            ·
              refine ⟨2349393738682821554306147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25060199879283429912598901 2349393738682821554306147)
              ·
                refine ⟨3524090608024232331459221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349393738682821554306147 3524090608024232331459221)
                ·
                  refine ⟨165191747251135890537151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3524090608024232331459221 165191747251135890537151)
                  ·
                    rfl

theorem cell23_2895388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_2895388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895388 prefixEnd_2895388 := by exact prefixLift 2895388
  have htrace : WordTrace (prefixWord ++ tailWord_2895388) baseStart_2895388 baseEnd_2895388 := by
    simpa [prefixWord, tailWord_2895388, baseEnd_2895388] using wordTrace_append hprefix tailTrace_2895388
  have hstable : (prefixWord ++ tailWord_2895388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895388).length < 2 ^ (prefixWord ++ tailWord_2895388).sum := by decide
  have hdescent : baseEnd_2895388 < baseStart_2895388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895408 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 2, 3, 2]
def baseStart_2895408 : Nat := 118140960795 + 2895408 * 2 ^ 59
def prefixEnd_2895408 : Nat := 4983230072969 + 3 ^ 40 * 2895408 * 2
def baseEnd_2895408 : Nat := 1486735994873312936584267

theorem tailTrace_2895408 : CollatzResearch.WordTrace tailWord_2895408 prefixEnd_2895408 1486735994873312936584267 := by
  unfold tailWord_2895408
  simp only [CollatzResearch.WordTrace]
  refine ⟨52802102747219393581323439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70402803662959191441764585 52802102747219393581323439)
  ·
    refine ⟨79203154120829090371985159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52802102747219393581323439 79203154120829090371985159)
    ·
      refine ⟨118804731181243635557977739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79203154120829090371985159 118804731181243635557977739)
      ·
        refine ⟨178207096771865453336966609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118804731181243635557977739 178207096771865453336966609)
        ·
          refine ⟨133655322578899090002724957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178207096771865453336966609 133655322578899090002724957)
          ·
            refine ⟨50120745967087158751021859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133655322578899090002724957 50120745967087158751021859)
            ·
              refine ⟨75181118950630738126532789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50120745967087158751021859 75181118950630738126532789)
              ·
                refine ⟨7048229901621631699362449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75181118950630738126532789 7048229901621631699362449)
                ·
                  refine ⟨5286172426216223774521837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048229901621631699362449 5286172426216223774521837)
                  ·
                    refine ⟨1982314659831083915445689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5286172426216223774521837 1982314659831083915445689)
                    ·
                      refine ⟨1486735994873312936584267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982314659831083915445689 1486735994873312936584267)
                      ·
                        rfl

theorem cell23_2895408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 3, 2].length) (baseStart_2895408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895408 prefixEnd_2895408 := by exact prefixLift 2895408
  have htrace : WordTrace (prefixWord ++ tailWord_2895408) baseStart_2895408 baseEnd_2895408 := by
    simpa [prefixWord, tailWord_2895408, baseEnd_2895408] using wordTrace_append hprefix tailTrace_2895408
  have hstable : (prefixWord ++ tailWord_2895408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895408).length < 2 ^ (prefixWord ++ tailWord_2895408).sum := by decide
  have hdescent : baseEnd_2895408 < baseStart_2895408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895425 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_2895425 : Nat := 118140960795 + 2895425 * 2 ^ 59
def prefixEnd_2895425 : Nat := 4983230072969 + 3 ^ 40 * 2895425 * 2
def baseEnd_2895425 : Nat := 1486744724044439370071689

theorem tailTrace_2895425 : CollatzResearch.WordTrace tailWord_2895425 prefixEnd_2895425 1486744724044439370071689 := by
  unfold tailWord_2895425
  simp only [CollatzResearch.WordTrace]
  refine ⟨105604825535377199066015729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70403217023584799377343819 105604825535377199066015729)
  ·
    refine ⟨79203619151532899299511797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105604825535377199066015729 79203619151532899299511797)
    ·
      refine ⟨7425339295456209309329231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79203619151532899299511797 7425339295456209309329231)
      ·
        refine ⟨11138008943184313963993847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7425339295456209309329231 11138008943184313963993847)
        ·
          refine ⟨16707013414776470945990771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138008943184313963993847 16707013414776470945990771)
          ·
            refine ⟨25060520122164706418986157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16707013414776470945990771 25060520122164706418986157)
            ·
              refine ⟨9397695045811764907119809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25060520122164706418986157 9397695045811764907119809)
              ·
                refine ⟨7048271284358823680339857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9397695045811764907119809 7048271284358823680339857)
                ·
                  refine ⟨5286203463269117760254893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048271284358823680339857 5286203463269117760254893)
                  ·
                    refine ⟨1982326298725919160095585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5286203463269117760254893 1982326298725919160095585)
                    ·
                      refine ⟨1486744724044439370071689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982326298725919160095585 1486744724044439370071689)
                      ·
                        rfl

theorem cell23_2895425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_2895425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895425 prefixEnd_2895425 := by exact prefixLift 2895425
  have htrace : WordTrace (prefixWord ++ tailWord_2895425) baseStart_2895425 baseEnd_2895425 := by
    simpa [prefixWord, tailWord_2895425, baseEnd_2895425] using wordTrace_append hprefix tailTrace_2895425
  have hstable : (prefixWord ++ tailWord_2895425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895425).length < 2 ^ (prefixWord ++ tailWord_2895425).sum := by decide
  have hdescent : baseEnd_2895425 < baseStart_2895425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895441 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2895441 : Nat := 118140960795 + 2895441 * 2 ^ 59
def prefixEnd_2895441 : Nat := 4983230072969 + 3 ^ 40 * 2895441 * 2
def baseEnd_2895441 : Nat := 1486752939734911307471615

theorem tailTrace_2895441 : CollatzResearch.WordTrace tailWord_2895441 prefixEnd_2895441 1486752939734911307471615 := by
  unfold tailWord_2895441
  simp only [CollatzResearch.WordTrace]
  refine ⟨105605409103319233798598177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70403606068879489199065451 105605409103319233798598177)
  ·
    refine ⟨79204056827489425348948633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105605409103319233798598177 79204056827489425348948633)
    ·
      refine ⟨59403042620617069011711475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79204056827489425348948633 59403042620617069011711475)
      ·
        refine ⟨89104563930925603517567213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59403042620617069011711475 89104563930925603517567213)
        ·
          refine ⟨33414211474097101319087705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89104563930925603517567213 33414211474097101319087705)
          ·
            refine ⟨25060658605572825989315779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33414211474097101319087705 25060658605572825989315779)
            ·
              refine ⟨37590987908359238983973669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25060658605572825989315779 37590987908359238983973669)
              ·
                refine ⟨7048310232817357309495063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37590987908359238983973669 7048310232817357309495063)
                ·
                  refine ⟨10572465349226035964242595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7048310232817357309495063 10572465349226035964242595)
                  ·
                    refine ⟨15858698023839053946363893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10572465349226035964242595 15858698023839053946363893)
                    ·
                      refine ⟨1486752939734911307471615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15858698023839053946363893 1486752939734911307471615)
                      ·
                        rfl

theorem cell23_2895441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2895441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895441 prefixEnd_2895441 := by exact prefixLift 2895441
  have htrace : WordTrace (prefixWord ++ tailWord_2895441) baseStart_2895441 baseEnd_2895441 := by
    simpa [prefixWord, tailWord_2895441, baseEnd_2895441] using wordTrace_append hprefix tailTrace_2895441
  have hstable : (prefixWord ++ tailWord_2895441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895441).length < 2 ^ (prefixWord ++ tailWord_2895441).sum := by decide
  have hdescent : baseEnd_2895441 < baseStart_2895441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895461 : List Nat := [1, 3, 1, 3, 3, 1, 2, 9]
def baseStart_2895461 : Nat := 118140960795 + 2895461 * 2 ^ 59
def prefixEnd_2895461 : Nat := 4983230072969 + 3 ^ 40 * 2895461 * 2
def baseEnd_2895461 : Nat := 55065304049925971452649

theorem tailTrace_2895461 : CollatzResearch.WordTrace tailWord_2895461 prefixEnd_2895461 55065304049925971452649 := by
  unfold tailWord_2895461
  simp only [CollatzResearch.WordTrace]
  refine ⟨105606138563246777214326237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70404092375497851476217491 105606138563246777214326237)
  ·
    refine ⟨39602301961217541455372339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105606138563246777214326237 39602301961217541455372339)
    ·
      refine ⟨59403452941826312183058509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39602301961217541455372339 59403452941826312183058509)
      ·
        refine ⟨22276294853184867068646941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59403452941826312183058509 22276294853184867068646941)
        ·
          refine ⟨8353610569944325150742603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22276294853184867068646941 8353610569944325150742603)
          ·
            refine ⟨12530415854916487726113905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353610569944325150742603 12530415854916487726113905)
            ·
              refine ⟨9397811891187365794585429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12530415854916487726113905 9397811891187365794585429)
              ·
                refine ⟨55065304049925971452649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9397811891187365794585429 55065304049925971452649)
                ·
                  rfl

theorem cell23_2895461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 9].length) (baseStart_2895461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895461 prefixEnd_2895461 := by exact prefixLift 2895461
  have htrace : WordTrace (prefixWord ++ tailWord_2895461) baseStart_2895461 baseEnd_2895461 := by
    simpa [prefixWord, tailWord_2895461, baseEnd_2895461] using wordTrace_append hprefix tailTrace_2895461
  have hstable : (prefixWord ++ tailWord_2895461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895461).length < 2 ^ (prefixWord ++ tailWord_2895461).sum := by decide
  have hdescent : baseEnd_2895461 < baseStart_2895461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895489 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2895489 : Nat := 118140960795 + 2895489 * 2 ^ 59
def prefixEnd_2895489 : Nat := 4983230072969 + 3 ^ 40 * 2895489 * 2
def baseEnd_2895489 : Nat := 1486777586806327119671395

theorem tailTrace_2895489 : CollatzResearch.WordTrace tailWord_2895489 prefixEnd_2895489 1486777586806327119671395 := by
  unfold tailWord_2895489
  simp only [CollatzResearch.WordTrace]
  refine ⟨105607159807145337996345521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70404773204763558664230347 105607159807145337996345521)
  ·
    refine ⟨79205369855359003497259141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105607159807145337996345521 79205369855359003497259141)
    ·
      refine ⟨14851006847879813155736089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79205369855359003497259141 14851006847879813155736089)
      ·
        refine ⟨11138255135909859866802067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14851006847879813155736089 11138255135909859866802067)
        ·
          refine ⟨16707382703864789800203101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138255135909859866802067 16707382703864789800203101)
          ·
            refine ⟨6265268513949296175076163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16707382703864789800203101 6265268513949296175076163)
            ·
              refine ⟨9397902770923944262614245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265268513949296175076163 9397902770923944262614245)
              ·
                refine ⟨1762106769548239549240171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9397902770923944262614245 1762106769548239549240171)
                ·
                  refine ⟨2643160154322359323860257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762106769548239549240171 2643160154322359323860257)
                  ·
                    refine ⟨1982370115741769492895193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2643160154322359323860257 1982370115741769492895193)
                    ·
                      refine ⟨1486777586806327119671395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982370115741769492895193 1486777586806327119671395)
                      ·
                        rfl

theorem cell23_2895489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2895489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895489 prefixEnd_2895489 := by exact prefixLift 2895489
  have htrace : WordTrace (prefixWord ++ tailWord_2895489) baseStart_2895489 baseEnd_2895489 := by
    simpa [prefixWord, tailWord_2895489, baseEnd_2895489] using wordTrace_append hprefix tailTrace_2895489
  have hstable : (prefixWord ++ tailWord_2895489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895489).length < 2 ^ (prefixWord ++ tailWord_2895489).sum := by decide
  have hdescent : baseEnd_2895489 < baseStart_2895489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895602 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_2895602 : Nat := 118140960795 + 2895602 * 2 ^ 59
def prefixEnd_2895602 : Nat := 4983230072969 + 3 ^ 40 * 2895602 * 2
def baseEnd_2895602 : Nat := 165203956680031686395375

theorem tailTrace_2895602 : CollatzResearch.WordTrace tailWord_2895602 prefixEnd_2895602 165203956680031686395375 := by
  unfold tailWord_2895602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26402820313933989573802265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70407520837157305530139373 26402820313933989573802265)
  ·
    refine ⟨19802115235450492180351699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26402820313933989573802265 19802115235450492180351699)
    ·
      refine ⟨29703172853175738270527549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19802115235450492180351699 29703172853175738270527549)
      ·
        refine ⟨11138689819940901851447831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29703172853175738270527549 11138689819940901851447831)
        ·
          refine ⟨16708034729911352777171747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138689819940901851447831 16708034729911352777171747)
          ·
            refine ⟨25062052094867029165757621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16708034729911352777171747 25062052094867029165757621)
            ·
              refine ⟨2349567383893783984289777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25062052094867029165757621 2349567383893783984289777)
              ·
                refine ⟨1762175537920337988217333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2349567383893783984289777 1762175537920337988217333)
                ·
                  refine ⟨165203956680031686395375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1762175537920337988217333 165203956680031686395375)
                  ·
                    rfl

theorem cell23_2895602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_2895602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895602 prefixEnd_2895602 := by exact prefixLift 2895602
  have htrace : WordTrace (prefixWord ++ tailWord_2895602) baseStart_2895602 baseEnd_2895602 := by
    simpa [prefixWord, tailWord_2895602, baseEnd_2895602] using wordTrace_append hprefix tailTrace_2895602
  have hstable : (prefixWord ++ tailWord_2895602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895602).length < 2 ^ (prefixWord ++ tailWord_2895602).sum := by decide
  have hdescent : baseEnd_2895602 < baseStart_2895602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895611 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 8]
def baseStart_2895611 : Nat := 118140960795 + 2895611 * 2 ^ 59
def prefixEnd_2895611 : Nat := 4983230072969 + 3 ^ 40 * 2895611 * 2
def baseEnd_2895611 : Nat := 495613410482058547448611

theorem tailTrace_2895611 : CollatzResearch.WordTrace tailWord_2895611 prefixEnd_2895611 495613410482058547448611 := by
  unfold tailWord_2895611
  simp only [CollatzResearch.WordTrace]
  refine ⟨105611609512703352832286687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70407739675135568554857791 105611609512703352832286687)
  ·
    refine ⟨158417414269055029248430031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105611609512703352832286687 158417414269055029248430031)
    ·
      refine ⟨237626121403582543872645047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158417414269055029248430031 237626121403582543872645047)
      ·
        refine ⟨356439182105373815808967571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237626121403582543872645047 356439182105373815808967571)
        ·
          refine ⟨534658773158060723713451357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356439182105373815808967571 534658773158060723713451357)
          ·
            refine ⟨200497039934272771392544259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 534658773158060723713451357 200497039934272771392544259)
            ·
              refine ⟨300745559901409157088816389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200497039934272771392544259 300745559901409157088816389)
              ·
                refine ⟨56389792481514216954153073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300745559901409157088816389 56389792481514216954153073)
                ·
                  refine ⟨42292344361135662715614805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56389792481514216954153073 42292344361135662715614805)
                  ·
                    refine ⟨495613410482058547448611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42292344361135662715614805 495613410482058547448611)
                    ·
                      rfl

theorem cell23_2895611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_2895611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895611 prefixEnd_2895611 := by exact prefixLift 2895611
  have htrace : WordTrace (prefixWord ++ tailWord_2895611) baseStart_2895611 baseEnd_2895611 := by
    simpa [prefixWord, tailWord_2895611, baseEnd_2895611] using wordTrace_append hprefix tailTrace_2895611
  have hstable : (prefixWord ++ tailWord_2895611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895611).length < 2 ^ (prefixWord ++ tailWord_2895611).sum := by decide
  have hdescent : baseEnd_2895611 < baseStart_2895611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895648 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2895648 : Nat := 118140960795 + 2895648 * 2 ^ 59
def prefixEnd_2895648 : Nat := 4983230072969 + 3 ^ 40 * 2895648 * 2
def baseEnd_2895648 : Nat := 1486859230230391997583163

theorem tailTrace_2895648 : CollatzResearch.WordTrace tailWord_2895648 prefixEnd_2895648 1486859230230391997583163 := by
  unfold tailWord_2895648
  simp only [CollatzResearch.WordTrace]
  refine ⟨52806479506784654075691799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70408639342379538767589065 52806479506784654075691799)
  ·
    refine ⟨79209719260176981113537699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52806479506784654075691799 79209719260176981113537699)
    ·
      refine ⟨118814578890265471670306549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79209719260176981113537699 118814578890265471670306549)
      ·
        refine ⟨11138866770962387969091239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118814578890265471670306549 11138866770962387969091239)
        ·
          refine ⟨16708300156443581953636859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11138866770962387969091239 16708300156443581953636859)
          ·
            refine ⟨25062450234665372930455289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16708300156443581953636859 25062450234665372930455289)
            ·
              refine ⟨18796837675999029697841467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25062450234665372930455289 18796837675999029697841467)
              ·
                refine ⟨28195256513998544546762201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18796837675999029697841467 28195256513998544546762201)
                ·
                  refine ⟨21146442385498908410071651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28195256513998544546762201 21146442385498908410071651)
                  ·
                    refine ⟨31719663578248362615107477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21146442385498908410071651 31719663578248362615107477)
                    ·
                      refine ⟨1486859230230391997583163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31719663578248362615107477 1486859230230391997583163)
                      ·
                        rfl

theorem cell23_2895648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2895648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895648 prefixEnd_2895648 := by exact prefixLift 2895648
  have htrace : WordTrace (prefixWord ++ tailWord_2895648) baseStart_2895648 baseEnd_2895648 := by
    simpa [prefixWord, tailWord_2895648, baseEnd_2895648] using wordTrace_append hprefix tailTrace_2895648
  have hstable : (prefixWord ++ tailWord_2895648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895648).length < 2 ^ (prefixWord ++ tailWord_2895648).sum := by decide
  have hdescent : baseEnd_2895648 < baseStart_2895648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895686 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2895686 : Nat := 118140960795 + 2895686 * 2 ^ 59
def prefixEnd_2895686 : Nat := 4983230072969 + 3 ^ 40 * 2895686 * 2
def baseEnd_2895686 : Nat := 1486878742495262848907989

theorem tailTrace_2895686 : CollatzResearch.WordTrace tailWord_2895686 prefixEnd_2895686 1486878742495262848907989 := by
  unfold tailWord_2895686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300448280857238770039591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70409563324954427094177941 3300448280857238770039591)
  ·
    refine ⟨4950672421285858155059387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300448280857238770039591 4950672421285858155059387)
    ·
      refine ⟨7426008631928787232589081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4950672421285858155059387 7426008631928787232589081)
      ·
        refine ⟨5569506473946590424441811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7426008631928787232589081 5569506473946590424441811)
        ·
          refine ⟨8354259710919885636662717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569506473946590424441811 8354259710919885636662717)
          ·
            refine ⟨3132847391594957113748519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8354259710919885636662717 3132847391594957113748519)
            ·
              refine ⟨4699271087392435670622779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132847391594957113748519 4699271087392435670622779)
              ·
                refine ⟨7048906631088653505934169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699271087392435670622779 7048906631088653505934169)
                ·
                  refine ⟨5286679973316490129450627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048906631088653505934169 5286679973316490129450627)
                  ·
                    refine ⟨7930019959974735194175941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286679973316490129450627 7930019959974735194175941)
                    ·
                      refine ⟨1486878742495262848907989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7930019959974735194175941 1486878742495262848907989)
                      ·
                        rfl

theorem cell23_2895686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2895686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895686 prefixEnd_2895686 := by exact prefixLift 2895686
  have htrace : WordTrace (prefixWord ++ tailWord_2895686) baseStart_2895686 baseEnd_2895686 := by
    simpa [prefixWord, tailWord_2895686, baseEnd_2895686] using wordTrace_append hprefix tailTrace_2895686
  have hstable : (prefixWord ++ tailWord_2895686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895686).length < 2 ^ (prefixWord ++ tailWord_2895686).sum := by decide
  have hdescent : baseEnd_2895686 < baseStart_2895686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895705 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 1, 5]
def baseStart_2895705 : Nat := 118140960795 + 2895705 * 2 ^ 59
def prefixEnd_2895705 : Nat := 4983230072969 + 3 ^ 40 * 2895705 * 2
def baseEnd_2895705 : Nat := 495629499542566091523467

theorem tailTrace_2895705 : CollatzResearch.WordTrace tailWord_2895705 prefixEnd_2895705 495629499542566091523467 := by
  unfold tailWord_2895705
  simp only [CollatzResearch.WordTrace]
  refine ⟨105615037974362806886208569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70410025316241871257472379 105615037974362806886208569)
  ·
    refine ⟨79211278480772105164656427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105615037974362806886208569 79211278480772105164656427)
    ·
      refine ⟨118816917721158157746984641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79211278480772105164656427 118816917721158157746984641)
      ·
        refine ⟨89112688290868618310238481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118816917721158157746984641 89112688290868618310238481)
        ·
          refine ⟨66834516218151463732678861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89112688290868618310238481 66834516218151463732678861)
          ·
            refine ⟨25062943581806798899754573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66834516218151463732678861 25062943581806798899754573)
            ·
              refine ⟨9398603843177549587407965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25062943581806798899754573 9398603843177549587407965)
              ·
                refine ⟨3524476441191581095277987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9398603843177549587407965 3524476441191581095277987)
                ·
                  refine ⟨5286714661787371642916981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524476441191581095277987 5286714661787371642916981)
                  ·
                    refine ⟨495629499542566091523467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5286714661787371642916981 495629499542566091523467)
                    ·
                      rfl

theorem cell23_2895705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_2895705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895705 prefixEnd_2895705 := by exact prefixLift 2895705
  have htrace : WordTrace (prefixWord ++ tailWord_2895705) baseStart_2895705 baseEnd_2895705 := by
    simpa [prefixWord, tailWord_2895705, baseEnd_2895705] using wordTrace_append hprefix tailTrace_2895705
  have hstable : (prefixWord ++ tailWord_2895705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895705).length < 2 ^ (prefixWord ++ tailWord_2895705).sum := by decide
  have hdescent : baseEnd_2895705 < baseStart_2895705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895719 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_2895719 : Nat := 118140960795 + 2895719 * 2 ^ 59
def prefixEnd_2895719 : Nat := 4983230072969 + 3 ^ 40 * 2895719 * 2
def baseEnd_2895719 : Nat := 1486895687356861219795337

theorem tailTrace_2895719 : CollatzResearch.WordTrace tailWord_2895719 prefixEnd_2895719 1486895687356861219795337 := by
  unfold tailWord_2895719
  simp only [CollatzResearch.WordTrace]
  refine ⟨105615548596312087277218211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70410365730874724851478807 105615548596312087277218211)
  ·
    refine ⟨158423322894468130915827317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105615548596312087277218211 158423322894468130915827317)
    ·
      refine ⟨14852186521356387273358811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158423322894468130915827317 14852186521356387273358811)
      ·
        refine ⟨22278279782034580910038217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14852186521356387273358811 22278279782034580910038217)
        ·
          refine ⟨16708709836525935682528663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22278279782034580910038217 16708709836525935682528663)
          ·
            refine ⟨25063064754788903523792995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16708709836525935682528663 25063064754788903523792995)
            ·
              refine ⟨37594597132183355285689493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25063064754788903523792995 37594597132183355285689493)
              ·
                refine ⟨1762246740571094779016695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37594597132183355285689493 1762246740571094779016695)
                ·
                  refine ⟨2643370110856642168525043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762246740571094779016695 2643370110856642168525043)
                  ·
                    refine ⟨3965055166284963252787565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2643370110856642168525043 3965055166284963252787565)
                    ·
                      refine ⟨1486895687356861219795337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3965055166284963252787565 1486895687356861219795337)
                      ·
                        rfl

theorem cell23_2895719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_2895719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895719 prefixEnd_2895719 := by exact prefixLift 2895719
  have htrace : WordTrace (prefixWord ++ tailWord_2895719) baseStart_2895719 baseEnd_2895719 := by
    simpa [prefixWord, tailWord_2895719, baseEnd_2895719] using wordTrace_append hprefix tailTrace_2895719
  have hstable : (prefixWord ++ tailWord_2895719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895719).length < 2 ^ (prefixWord ++ tailWord_2895719).sum := by decide
  have hdescent : baseEnd_2895719 < baseStart_2895719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895725 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2895725 : Nat := 118140960795 + 2895725 * 2 ^ 59
def prefixEnd_2895725 : Nat := 4983230072969 + 3 ^ 40 * 2895725 * 2
def baseEnd_2895725 : Nat := 1486898768240788196320309

theorem tailTrace_2895725 : CollatzResearch.WordTrace tailWord_2895725 prefixEnd_2895725 1486898768240788196320309 := by
  unfold tailWord_2895725
  simp only [CollatzResearch.WordTrace]
  refine ⟨105615767434290350301936629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70410511622860233534624419 105615767434290350301936629)
  ·
    refine ⟨9901478196964720340806559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105615767434290350301936629 9901478196964720340806559)
    ·
      refine ⟨14852217295447080511209839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9901478196964720340806559 14852217295447080511209839)
      ·
        refine ⟨22278325943170620766814759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14852217295447080511209839 22278325943170620766814759)
        ·
          refine ⟨33417488914755931150222139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22278325943170620766814759 33417488914755931150222139)
          ·
            refine ⟨50126233372133896725333209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33417488914755931150222139 50126233372133896725333209)
            ·
              refine ⟨37594675029100422543999907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50126233372133896725333209 37594675029100422543999907)
              ·
                refine ⟨56392012543650633815999861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37594675029100422543999907 56392012543650633815999861)
                ·
                  refine ⟨5286751175967246920249987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56392012543650633815999861 5286751175967246920249987)
                  ·
                    refine ⟨7930126763950870380374981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5286751175967246920249987 7930126763950870380374981)
                    ·
                      refine ⟨1486898768240788196320309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7930126763950870380374981 1486898768240788196320309)
                      ·
                        rfl

theorem cell23_2895725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2895725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895725 prefixEnd_2895725 := by exact prefixLift 2895725
  have htrace : WordTrace (prefixWord ++ tailWord_2895725) baseStart_2895725 baseEnd_2895725 := by
    simpa [prefixWord, tailWord_2895725, baseEnd_2895725] using wordTrace_append hprefix tailTrace_2895725
  have hstable : (prefixWord ++ tailWord_2895725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895725).length < 2 ^ (prefixWord ++ tailWord_2895725).sum := by decide
  have hdescent : baseEnd_2895725 < baseStart_2895725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895762 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2895762 : Nat := 118140960795 + 2895762 * 2 ^ 59
def prefixEnd_2895762 : Nat := 4983230072969 + 3 ^ 40 * 2895762 * 2
def baseEnd_2895762 : Nat := 1486917767025004551557639

theorem tailTrace_2895762 : CollatzResearch.WordTrace tailWord_2895762 prefixEnd_2895762 1486917767025004551557639 := by
  unfold tailWord_2895762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26404279233789076405258385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70411411290104203747355693 26404279233789076405258385)
  ·
    refine ⟨19803209425341807303943789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26404279233789076405258385 19803209425341807303943789)
    ·
      refine ⟨7426203534503177738978921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19803209425341807303943789 7426203534503177738978921)
      ·
        refine ⟨5569652650877383304234191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7426203534503177738978921 5569652650877383304234191)
        ·
          refine ⟨8354478976316074956351287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569652650877383304234191 8354478976316074956351287)
          ·
            refine ⟨12531718464474112434526931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8354478976316074956351287 12531718464474112434526931)
            ·
              refine ⟨18797577696711168651790397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12531718464474112434526931 18797577696711168651790397)
              ·
                refine ⟨7049091636266688244421399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18797577696711168651790397 7049091636266688244421399)
                ·
                  refine ⟨10573637454400032366632099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7049091636266688244421399 10573637454400032366632099)
                  ·
                    refine ⟨15860456181600048549948149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10573637454400032366632099 15860456181600048549948149)
                    ·
                      refine ⟨1486917767025004551557639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15860456181600048549948149 1486917767025004551557639)
                      ·
                        rfl

theorem cell23_2895762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2895762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895762 prefixEnd_2895762 := by exact prefixLift 2895762
  have htrace : WordTrace (prefixWord ++ tailWord_2895762) baseStart_2895762 baseEnd_2895762 := by
    simpa [prefixWord, tailWord_2895762, baseEnd_2895762] using wordTrace_append hprefix tailTrace_2895762
  have hstable : (prefixWord ++ tailWord_2895762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895762).length < 2 ^ (prefixWord ++ tailWord_2895762).sum := by decide
  have hdescent : baseEnd_2895762 < baseStart_2895762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895790 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2895790 : Nat := 118140960795 + 2895790 * 2 ^ 59
def prefixEnd_2895790 : Nat := 4983230072969 + 3 ^ 40 * 2895790 * 2
def baseEnd_2895790 : Nat := 495644048161110147335837

theorem tailTrace_2895790 : CollatzResearch.WordTrace tailWord_2895790 prefixEnd_2895790 495644048161110147335837 := by
  unfold tailWord_2895790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13202267272381858300381603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70412092119369910935368549 13202267272381858300381603)
  ·
    refine ⟨19803400908572787450572405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13202267272381858300381603 19803400908572787450572405)
    ·
      refine ⟨1856568835178698823491163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19803400908572787450572405 1856568835178698823491163)
      ·
        refine ⟨2784853252768048235236745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856568835178698823491163 2784853252768048235236745)
        ·
          refine ⟨2088639939576036176427559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2784853252768048235236745 2088639939576036176427559)
          ·
            refine ⟨3132959909364054264641339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088639939576036176427559 3132959909364054264641339)
            ·
              refine ⟨4699439864046081396962009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132959909364054264641339 4699439864046081396962009)
              ·
                refine ⟨3524579898034561047721507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4699439864046081396962009 3524579898034561047721507)
                ·
                  refine ⟨5286869847051841571582261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524579898034561047721507 5286869847051841571582261)
                  ·
                    refine ⟨495644048161110147335837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5286869847051841571582261 495644048161110147335837)
                    ·
                      rfl

theorem cell23_2895790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2895790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895790 prefixEnd_2895790 := by exact prefixLift 2895790
  have htrace : WordTrace (prefixWord ++ tailWord_2895790) baseStart_2895790 baseEnd_2895790 := by
    simpa [prefixWord, tailWord_2895790, baseEnd_2895790] using wordTrace_append hprefix tailTrace_2895790
  have hstable : (prefixWord ++ tailWord_2895790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895790).length < 2 ^ (prefixWord ++ tailWord_2895790).sum := by decide
  have hdescent : baseEnd_2895790 < baseStart_2895790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895796 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2895796 : Nat := 118140960795 + 2895796 * 2 ^ 59
def prefixEnd_2895796 : Nat := 4983230072969 + 3 ^ 40 * 2895796 * 2
def baseEnd_2895796 : Nat := 1486935225367257418532483

theorem tailTrace_2895796 : CollatzResearch.WordTrace tailWord_2895796 prefixEnd_2895796 1486935225367257418532483 := by
  unfold tailWord_2895796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52809178508516564713885621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70412238011355419618514161 52809178508516564713885621)
  ·
    refine ⟨4950860485173427941926777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52809178508516564713885621 4950860485173427941926777)
    ·
      refine ⟨3713145363880070956445083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4950860485173427941926777 3713145363880070956445083)
      ·
        refine ⟨5569718045820106434667625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3713145363880070956445083 5569718045820106434667625)
        ·
          refine ⟨4177288534365079826000719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5569718045820106434667625 4177288534365079826000719)
          ·
            refine ⟨6265932801547619739001079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4177288534365079826000719 6265932801547619739001079)
            ·
              refine ⟨9398899202321429608501619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6265932801547619739001079 9398899202321429608501619)
              ·
                refine ⟨14098348803482144412752429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9398899202321429608501619 14098348803482144412752429)
                ·
                  refine ⟨5286880801305804154782161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14098348803482144412752429 5286880801305804154782161)
                  ·
                    refine ⟨3965160600979353116086621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5286880801305804154782161 3965160600979353116086621)
                    ·
                      refine ⟨1486935225367257418532483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3965160600979353116086621 1486935225367257418532483)
                      ·
                        rfl

theorem cell23_2895796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2895796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895796 prefixEnd_2895796 := by exact prefixLift 2895796
  have htrace : WordTrace (prefixWord ++ tailWord_2895796) baseStart_2895796 baseEnd_2895796 := by
    simpa [prefixWord, tailWord_2895796, baseEnd_2895796] using wordTrace_append hprefix tailTrace_2895796
  have hstable : (prefixWord ++ tailWord_2895796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895796).length < 2 ^ (prefixWord ++ tailWord_2895796).sum := by decide
  have hdescent : baseEnd_2895796 < baseStart_2895796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895832 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 3, 4, 2]
def baseStart_2895832 : Nat := 118140960795 + 2895832 * 2 ^ 59
def prefixEnd_2895832 : Nat := 4983230072969 + 3 ^ 40 * 2895832 * 2
def baseEnd_2895832 : Nat := 1486953710670819277682317

theorem tailTrace_2895832 : CollatzResearch.WordTrace tailWord_2895832 prefixEnd_2895832 1486953710670819277682317 := by
  unfold tailWord_2895832
  simp only [CollatzResearch.WordTrace]
  refine ⟨52809835022451353788040875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70413113363268471717387833 52809835022451353788040875)
  ·
    refine ⟨79214752533677030682061313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52809835022451353788040875 79214752533677030682061313)
    ·
      refine ⟨59411064400257773011545985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79214752533677030682061313 59411064400257773011545985)
      ·
        refine ⟨44558298300193329758659489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59411064400257773011545985 44558298300193329758659489)
        ·
          refine ⟨33418723725144997318994617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44558298300193329758659489 33418723725144997318994617)
          ·
            refine ⟨25064042793858747989245963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33418723725144997318994617 25064042793858747989245963)
            ·
              refine ⟨37596064190788121983868945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25064042793858747989245963 37596064190788121983868945)
              ·
                refine ⟨28197048143091091487901709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37596064190788121983868945 28197048143091091487901709)
                ·
                  refine ⟨10573893053659159307963141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28197048143091091487901709 10573893053659159307963141)
                  ·
                    refine ⟨1982604947561092370243089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10573893053659159307963141 1982604947561092370243089)
                    ·
                      refine ⟨1486953710670819277682317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982604947561092370243089 1486953710670819277682317)
                      ·
                        rfl

theorem cell23_2895832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_2895832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895832 prefixEnd_2895832 := by exact prefixLift 2895832
  have htrace : WordTrace (prefixWord ++ tailWord_2895832) baseStart_2895832 baseEnd_2895832 := by
    simpa [prefixWord, tailWord_2895832, baseEnd_2895832] using wordTrace_append hprefix tailTrace_2895832
  have hstable : (prefixWord ++ tailWord_2895832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895832).length < 2 ^ (prefixWord ++ tailWord_2895832).sum := by decide
  have hdescent : baseEnd_2895832 < baseStart_2895832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895855 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 7]
def baseStart_2895855 : Nat := 118140960795 + 2895855 * 2 ^ 59
def prefixEnd_2895855 : Nat := 4983230072969 + 3 ^ 40 * 2895855 * 2
def baseEnd_2895855 : Nat := 165218391191763631966079

theorem tailTrace_2895855 : CollatzResearch.WordTrace tailWord_2895855 prefixEnd_2895855 165218391191763631966079 := by
  unfold tailWord_2895855
  simp only [CollatzResearch.WordTrace]
  refine ⟨105620508923819382504169019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70413672615879588336112679 105620508923819382504169019)
  ·
    refine ⟨158430763385729073756253529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105620508923819382504169019 158430763385729073756253529)
    ·
      refine ⟨118823072539296805317190147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158430763385729073756253529 118823072539296805317190147)
      ·
        refine ⟨178234608808945207975785221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118823072539296805317190147 178234608808945207975785221)
        ·
          refine ⟨33418989151677226495459729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178234608808945207975785221 33418989151677226495459729)
          ·
            refine ⟨25064241863757919871594797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33418989151677226495459729 25064241863757919871594797)
            ·
              refine ⟨9399090698909219951848049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25064241863757919871594797 9399090698909219951848049)
              ·
                refine ⟨7049318024181914963886037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9399090698909219951848049 7049318024181914963886037)
                ·
                  refine ⟨165218391191763631966079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7049318024181914963886037 165218391191763631966079)
                  ·
                    rfl

theorem cell23_2895855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 7].length) (baseStart_2895855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895855 prefixEnd_2895855 := by exact prefixLift 2895855
  have htrace : WordTrace (prefixWord ++ tailWord_2895855) baseStart_2895855 baseEnd_2895855 := by
    simpa [prefixWord, tailWord_2895855, baseEnd_2895855] using wordTrace_append hprefix tailTrace_2895855
  have hstable : (prefixWord ++ tailWord_2895855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895855).length < 2 ^ (prefixWord ++ tailWord_2895855).sum := by decide
  have hdescent : baseEnd_2895855 < baseStart_2895855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895870 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2895870 : Nat := 118140960795 + 2895870 * 2 ^ 59
def prefixEnd_2895870 : Nat := 4983230072969 + 3 ^ 40 * 2895870 * 2
def baseEnd_2895870 : Nat := 1486973222935690129007143

theorem tailTrace_2895870 : CollatzResearch.WordTrace tailWord_2895870 prefixEnd_2895870 1486973222935690129007143 := by
  unfold tailWord_2895870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13202632002345630008245633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70414037345843360043976709 13202632002345630008245633)
  ·
    refine ⟨9901974001759222506184225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13202632002345630008245633 9901974001759222506184225)
    ·
      refine ⟨7426480501319416879638169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9901974001759222506184225 7426480501319416879638169)
      ·
        refine ⟨5569860375989562659728627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7426480501319416879638169 5569860375989562659728627)
        ·
          refine ⟨8354790563984343989592941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5569860375989562659728627 8354790563984343989592941)
          ·
            refine ⟨3133046461494128996097353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8354790563984343989592941 3133046461494128996097353)
            ·
              refine ⟨2349784846120596747073015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3133046461494128996097353 2349784846120596747073015)
              ·
                refine ⟨3524677269180895120609523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349784846120596747073015 3524677269180895120609523)
                ·
                  refine ⟨5287015903771342680914285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3524677269180895120609523 5287015903771342680914285)
                  ·
                    refine ⟨1982630963914253505342857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5287015903771342680914285 1982630963914253505342857)
                    ·
                      refine ⟨1486973222935690129007143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982630963914253505342857 1486973222935690129007143)
                      ·
                        rfl

theorem cell23_2895870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2895870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895870 prefixEnd_2895870 := by exact prefixLift 2895870
  have htrace : WordTrace (prefixWord ++ tailWord_2895870) baseStart_2895870 baseEnd_2895870 := by
    simpa [prefixWord, tailWord_2895870, baseEnd_2895870] using wordTrace_append hprefix tailTrace_2895870
  have hstable : (prefixWord ++ tailWord_2895870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895870).length < 2 ^ (prefixWord ++ tailWord_2895870).sum := by decide
  have hdescent : baseEnd_2895870 < baseStart_2895870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895922 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_2895922 : Nat := 118140960795 + 2895922 * 2 ^ 59
def prefixEnd_2895922 : Nat := 4983230072969 + 3 ^ 40 * 2895922 * 2
def baseEnd_2895922 : Nat := 1486999923929723925556903

theorem tailTrace_2895922 : CollatzResearch.WordTrace tailWord_2895922 prefixEnd_2895922 1486999923929723925556903 := by
  unfold tailWord_2895922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26405738153644163236714505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70415301743051101964572013 26405738153644163236714505)
  ·
    refine ⟨19804303615233122427535879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26405738153644163236714505 19804303615233122427535879)
    ·
      refine ⟨29706455422849683641303819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19804303615233122427535879 29706455422849683641303819)
      ·
        refine ⟨44559683134274525461955729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29706455422849683641303819 44559683134274525461955729)
        ·
          refine ⟨33419762350705894096466797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44559683134274525461955729 33419762350705894096466797)
          ·
            refine ⟨12532410881514710286175049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33419762350705894096466797 12532410881514710286175049)
            ·
              refine ⟨9399308161136032714631287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12532410881514710286175049 9399308161136032714631287)
              ·
                refine ⟨14098962241704049071946931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9399308161136032714631287 14098962241704049071946931)
                ·
                  refine ⟨21148443362556073607920397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14098962241704049071946931 21148443362556073607920397)
                  ·
                    refine ⟨7930666260958527602970149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21148443362556073607920397 7930666260958527602970149)
                    ·
                      refine ⟨1486999923929723925556903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7930666260958527602970149 1486999923929723925556903)
                      ·
                        rfl

theorem cell23_2895922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_2895922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895922 prefixEnd_2895922 := by exact prefixLift 2895922
  have htrace : WordTrace (prefixWord ++ tailWord_2895922) baseStart_2895922 baseEnd_2895922 := by
    simpa [prefixWord, tailWord_2895922, baseEnd_2895922] using wordTrace_append hprefix tailTrace_2895922
  have hstable : (prefixWord ++ tailWord_2895922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895922).length < 2 ^ (prefixWord ++ tailWord_2895922).sum := by decide
  have hdescent : baseEnd_2895922 < baseStart_2895922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895935 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_2895935 : Nat := 118140960795 + 2895935 * 2 ^ 59
def prefixEnd_2895935 : Nat := 4983230072969 + 3 ^ 40 * 2895935 * 2
def baseEnd_2895935 : Nat := 1487006599178232374694343

theorem tailTrace_2895935 : CollatzResearch.WordTrace tailWord_2895935 prefixEnd_2895935 1487006599178232374694343 := by
  unfold tailWord_2895935
  simp only [CollatzResearch.WordTrace]
  refine ⟨105623426763529556167081259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70415617842353037444720839 105623426763529556167081259)
  ·
    refine ⟨158435140145294334250621889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105623426763529556167081259 158435140145294334250621889)
    ·
      refine ⟨118826355108970750687966417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158435140145294334250621889 118826355108970750687966417)
      ·
        refine ⟨89119766331728063015974813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118826355108970750687966417 89119766331728063015974813)
        ·
          refine ⟨33419912374398023630990555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89119766331728063015974813 33419912374398023630990555)
          ·
            refine ⟨50129868561597035446485833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33419912374398023630990555 50129868561597035446485833)
            ·
              refine ⟨37597401421197776584864375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50129868561597035446485833 37597401421197776584864375)
              ·
                refine ⟨56396102131796664877296563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37597401421197776584864375 56396102131796664877296563)
                ·
                  refine ⟨84594153197694997315944845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56396102131796664877296563 84594153197694997315944845)
                  ·
                    refine ⟨31722807449135623993479317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84594153197694997315944845 31722807449135623993479317)
                    ·
                      refine ⟨1487006599178232374694343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31722807449135623993479317 1487006599178232374694343)
                      ·
                        rfl

theorem cell23_2895935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_2895935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895935 prefixEnd_2895935 := by exact prefixLift 2895935
  have htrace : WordTrace (prefixWord ++ tailWord_2895935) baseStart_2895935 baseEnd_2895935 := by
    simpa [prefixWord, tailWord_2895935, baseEnd_2895935] using wordTrace_append hprefix tailTrace_2895935
  have hstable : (prefixWord ++ tailWord_2895935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895935).length < 2 ^ (prefixWord ++ tailWord_2895935).sum := by decide
  have hdescent : baseEnd_2895935 < baseStart_2895935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895945 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 8]
def baseStart_2895945 : Nat := 118140960795 + 2895945 * 2 ^ 59
def prefixEnd_2895945 : Nat := 4983230072969 + 3 ^ 40 * 2895945 * 2
def baseEnd_2895945 : Nat := 165223525998308592841033

theorem tailTrace_2895945 : CollatzResearch.WordTrace tailWord_2895945 prefixEnd_2895945 165223525998308592841033 := by
  unfold tailWord_2895945
  simp only [CollatzResearch.WordTrace]
  refine ⟨105623791493493327874945289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70415860995662218583296859 105623791493493327874945289)
  ·
    refine ⟨79217843620119995906208967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105623791493493327874945289 79217843620119995906208967)
    ·
      refine ⟨118826765430179993859313451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79217843620119995906208967 118826765430179993859313451)
      ·
        refine ⟨178240148145269990788970177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118826765430179993859313451 178240148145269990788970177)
        ·
          refine ⟨133680111108952493091727633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178240148145269990788970177 133680111108952493091727633)
          ·
            refine ⟨100260083331714369818795725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133680111108952493091727633 100260083331714369818795725)
            ·
              refine ⟨37597531249392888682048397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100260083331714369818795725 37597531249392888682048397)
              ·
                refine ⟨14099074218522333255768149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37597531249392888682048397 14099074218522333255768149)
                ·
                  refine ⟨165223525998308592841033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14099074218522333255768149 165223525998308592841033)
                  ·
                    rfl

theorem cell23_2895945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_2895945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895945 prefixEnd_2895945 := by exact prefixLift 2895945
  have htrace : WordTrace (prefixWord ++ tailWord_2895945) baseStart_2895945 baseEnd_2895945 := by
    simpa [prefixWord, tailWord_2895945, baseEnd_2895945] using wordTrace_append hprefix tailTrace_2895945
  have hstable : (prefixWord ++ tailWord_2895945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895945).length < 2 ^ (prefixWord ++ tailWord_2895945).sum := by decide
  have hdescent : baseEnd_2895945 < baseStart_2895945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895962 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_2895962 : Nat := 118140960795 + 2895962 * 2 ^ 59
def prefixEnd_2895962 : Nat := 4983230072969 + 3 ^ 40 * 2895962 * 2
def baseEnd_2895962 : Nat := 165224495906211529895191

theorem tailTrace_2895962 : CollatzResearch.WordTrace tailWord_2895962 prefixEnd_2895962 165224495906211529895191 := by
  unfold tailWord_2895962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26406102883607934944578535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70416274356287826518876093 26406102883607934944578535)
  ·
    refine ⟨39609154325411902416867803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26406102883607934944578535 39609154325411902416867803)
    ·
      refine ⟨59413731488117853625301705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39609154325411902416867803 59413731488117853625301705)
      ·
        refine ⟨44560298616088390218976279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59413731488117853625301705 44560298616088390218976279)
        ·
          refine ⟨66840447924132585328464419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44560298616088390218976279 66840447924132585328464419)
          ·
            refine ⟨100260671886198877992696629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66840447924132585328464419 100260671886198877992696629)
            ·
              refine ⟨9399437989331144811815309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100260671886198877992696629 9399437989331144811815309)
              ·
                refine ⟨3524789245999179304430741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9399437989331144811815309 3524789245999179304430741)
                ·
                  refine ⟨165224495906211529895191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3524789245999179304430741 165224495906211529895191)
                  ·
                    rfl

theorem cell23_2895962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_2895962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895962 prefixEnd_2895962 := by exact prefixLift 2895962
  have htrace : WordTrace (prefixWord ++ tailWord_2895962) baseStart_2895962 baseEnd_2895962 := by
    simpa [prefixWord, tailWord_2895962, baseEnd_2895962] using wordTrace_append hprefix tailTrace_2895962
  have hstable : (prefixWord ++ tailWord_2895962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895962).length < 2 ^ (prefixWord ++ tailWord_2895962).sum := by decide
  have hdescent : baseEnd_2895962 < baseStart_2895962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2895972 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_2895972 : Nat := 118140960795 + 2895972 * 2 ^ 59
def prefixEnd_2895972 : Nat := 4983230072969 + 3 ^ 40 * 2895972 * 2
def baseEnd_2895972 : Nat := 1487025597962448729931673

theorem tailTrace_2895972 : CollatzResearch.WordTrace tailWord_2895972 prefixEnd_2895972 1487025597962448729931673 := by
  unfold tailWord_2895972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52812388132197755743089085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70416517509597007657452113 52812388132197755743089085)
  ·
    refine ⟨19804645549574158403658407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52812388132197755743089085 19804645549574158403658407)
    ·
      refine ⟨29706968324361237605487611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19804645549574158403658407 29706968324361237605487611)
      ·
        refine ⟨44560452486541856408231417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29706968324361237605487611 44560452486541856408231417)
        ·
          refine ⟨33420339364906392306173563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44560452486541856408231417 33420339364906392306173563)
          ·
            refine ⟨50130509047359588459260345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33420339364906392306173563 50130509047359588459260345)
            ·
              refine ⟨37597881785519691344445259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50130509047359588459260345 37597881785519691344445259)
              ·
                refine ⟨56396822678279537016667889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37597881785519691344445259 56396822678279537016667889)
                ·
                  refine ⟨42297617008709652762500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56396822678279537016667889 42297617008709652762500917)
                  ·
                    refine ⟨3965401594566529946484461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42297617008709652762500917 3965401594566529946484461)
                    ·
                      refine ⟨1487025597962448729931673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3965401594566529946484461 1487025597962448729931673)
                      ·
                        rfl

theorem cell23_2895972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_2895972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2895972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2895972 prefixEnd_2895972 := by exact prefixLift 2895972
  have htrace : WordTrace (prefixWord ++ tailWord_2895972) baseStart_2895972 baseEnd_2895972 := by
    simpa [prefixWord, tailWord_2895972, baseEnd_2895972] using wordTrace_append hprefix tailTrace_2895972
  have hstable : (prefixWord ++ tailWord_2895972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2895972).length < 2 ^ (prefixWord ++ tailWord_2895972).sum := by decide
  have hdescent : baseEnd_2895972 < baseStart_2895972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2895972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896029 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2896029 : Nat := 118140960795 + 2896029 * 2 ^ 59
def prefixEnd_2896029 : Nat := 4983230072969 + 3 ^ 40 * 2896029 * 2
def baseEnd_2896029 : Nat := 1487054866359755006918911

theorem tailTrace_2896029 : CollatzResearch.WordTrace tailWord_2896029 prefixEnd_2896029 1487054866359755006918911 := by
  unfold tailWord_2896029
  simp only [CollatzResearch.WordTrace]
  refine ⟨105626855225189010221003141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70417903483459340147335427 105626855225189010221003141)
  ·
    refine ⟨19805035354722939416438089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105626855225189010221003141 19805035354722939416438089)
    ·
      refine ⟨14853776516042204562328567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19805035354722939416438089 14853776516042204562328567)
      ·
        refine ⟨22280664774063306843492851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14853776516042204562328567 22280664774063306843492851)
        ·
          refine ⟨33420997161094960265239277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22280664774063306843492851 33420997161094960265239277)
          ·
            refine ⟨12532873935410610099464729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33420997161094960265239277 12532873935410610099464729)
            ·
              refine ⟨9399655451557957574598547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12532873935410610099464729 9399655451557957574598547)
              ·
                refine ⟨14099483177336936361897821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9399655451557957574598547 14099483177336936361897821)
                ·
                  refine ⟨5287306191501351135711683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14099483177336936361897821 5287306191501351135711683)
                  ·
                    refine ⟨7930959287252026703567525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5287306191501351135711683 7930959287252026703567525)
                    ·
                      refine ⟨1487054866359755006918911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7930959287252026703567525 1487054866359755006918911)
                      ·
                        rfl

theorem cell23_2896029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2896029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896029 prefixEnd_2896029 := by exact prefixLift 2896029
  have htrace : WordTrace (prefixWord ++ tailWord_2896029) baseStart_2896029 baseEnd_2896029 := by
    simpa [prefixWord, tailWord_2896029, baseEnd_2896029] using wordTrace_append hprefix tailTrace_2896029
  have hstable : (prefixWord ++ tailWord_2896029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896029).length < 2 ^ (prefixWord ++ tailWord_2896029).sum := by decide
  have hdescent : baseEnd_2896029 < baseStart_2896029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896033 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2896033 : Nat := 118140960795 + 2896033 * 2 ^ 59
def prefixEnd_2896033 : Nat := 4983230072969 + 3 ^ 40 * 2896033 * 2
def baseEnd_2896033 : Nat := 1487056920282372991268893

theorem tailTrace_2896033 : CollatzResearch.WordTrace tailWord_2896033 prefixEnd_2896033 1487056920282372991268893 := by
  unfold tailWord_2896033
  simp only [CollatzResearch.WordTrace]
  refine ⟨105627001117174518904148753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70418000744783012602765835 105627001117174518904148753)
  ·
    refine ⟨79220250837880889178111565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105627001117174518904148753 79220250837880889178111565)
    ·
      refine ⟨29707594064205333441791837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79220250837880889178111565 29707594064205333441791837)
      ·
        refine ⟨11140347774077000040671939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29707594064205333441791837 11140347774077000040671939)
        ·
          refine ⟨16710521661115500061007909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11140347774077000040671939 16710521661115500061007909)
          ·
            refine ⟨3133222811459156261438983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16710521661115500061007909 3133222811459156261438983)
            ·
              refine ⟨4699834217188734392158475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133222811459156261438983 4699834217188734392158475)
              ·
                refine ⟨7049751325783101588237713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4699834217188734392158475 7049751325783101588237713)
                ·
                  refine ⟨5287313494337326191178285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7049751325783101588237713 5287313494337326191178285)
                  ·
                    refine ⟨1982742560376497321691857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5287313494337326191178285 1982742560376497321691857)
                    ·
                      refine ⟨1487056920282372991268893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982742560376497321691857 1487056920282372991268893)
                      ·
                        rfl

theorem cell23_2896033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2896033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896033 prefixEnd_2896033 := by exact prefixLift 2896033
  have htrace : WordTrace (prefixWord ++ tailWord_2896033) baseStart_2896033 baseEnd_2896033 := by
    simpa [prefixWord, tailWord_2896033, baseEnd_2896033] using wordTrace_append hprefix tailTrace_2896033
  have hstable : (prefixWord ++ tailWord_2896033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896033).length < 2 ^ (prefixWord ++ tailWord_2896033).sum := by decide
  have hdescent : baseEnd_2896033 < baseStart_2896033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896076 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2896076 : Nat := 118140960795 + 2896076 * 2 ^ 59
def prefixEnd_2896076 : Nat := 4983230072969 + 3 ^ 40 * 2896076 * 2
def baseEnd_2896076 : Nat := 1487078999950516323031195

theorem tailTrace_2896076 : CollatzResearch.WordTrace tailWord_2896076 prefixEnd_2896076 1487078999950516323031195 := by
  unfold tailWord_2896076
  simp only [CollatzResearch.WordTrace]
  refine ⟨52814284728009368623982041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70419046304012491498642721 52814284728009368623982041)
  ·
    refine ⟨39610713546007026467986531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52814284728009368623982041 39610713546007026467986531)
    ·
      refine ⟨59416070319010539701979797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39610713546007026467986531 59416070319010539701979797)
      ·
        refine ⟨2785128296203619048530303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59416070319010539701979797 2785128296203619048530303)
        ·
          refine ⟨4177692444305428572795455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785128296203619048530303 4177692444305428572795455)
          ·
            refine ⟨6266538666458142859193183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4177692444305428572795455 6266538666458142859193183)
            ·
              refine ⟨9399807999687214288789775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266538666458142859193183 9399807999687214288789775)
              ·
                refine ⟨14099711999530821433184663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9399807999687214288789775 14099711999530821433184663)
                ·
                  refine ⟨21149567999296232149776995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14099711999530821433184663 21149567999296232149776995)
                  ·
                    refine ⟨31724351998944348224665493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21149567999296232149776995 31724351998944348224665493)
                    ·
                      refine ⟨1487078999950516323031195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31724351998944348224665493 1487078999950516323031195)
                      ·
                        rfl

theorem cell23_2896076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2896076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896076 prefixEnd_2896076 := by exact prefixLift 2896076
  have htrace : WordTrace (prefixWord ++ tailWord_2896076) baseStart_2896076 baseEnd_2896076 := by
    simpa [prefixWord, tailWord_2896076, baseEnd_2896076] using wordTrace_append hprefix tailTrace_2896076
  have hstable : (prefixWord ++ tailWord_2896076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896076).length < 2 ^ (prefixWord ++ tailWord_2896076).sum := by decide
  have hdescent : baseEnd_2896076 < baseStart_2896076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896086 : List Nat := [5, 2, 1, 2, 1, 2, 1, 9]
def baseStart_2896086 : Nat := 118140960795 + 2896086 * 2 ^ 59
def prefixEnd_2896086 : Nat := 4983230072969 + 3 ^ 40 * 2896086 * 2
def baseEnd_2896086 : Nat := 55077190176187454959487

theorem tailTrace_2896086 : CollatzResearch.WordTrace tailWord_2896086 prefixEnd_2896086 55077190176187454959487 := by
  unfold tailWord_2896086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6601808386623906809739257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70419289457321672637218741 6601808386623906809739257)
  ·
    refine ⟨4951356289967930107304443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6601808386623906809739257 4951356289967930107304443)
    ·
      refine ⟨7427034434951895160956665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951356289967930107304443 7427034434951895160956665)
      ·
        refine ⟨5570275826213921370717499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7427034434951895160956665 5570275826213921370717499)
        ·
          refine ⟨8355413739320882056076249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570275826213921370717499 8355413739320882056076249)
          ·
            refine ⟨6266560304490661542057187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8355413739320882056076249 6266560304490661542057187)
            ·
              refine ⟨9399840456735992313085781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266560304490661542057187 9399840456735992313085781)
              ·
                refine ⟨55077190176187454959487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9399840456735992313085781 55077190176187454959487)
                ·
                  rfl

theorem cell23_2896086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_2896086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896086 prefixEnd_2896086 := by exact prefixLift 2896086
  have htrace : WordTrace (prefixWord ++ tailWord_2896086) baseStart_2896086 baseEnd_2896086 := by
    simpa [prefixWord, tailWord_2896086, baseEnd_2896086] using wordTrace_append hprefix tailTrace_2896086
  have hstable : (prefixWord ++ tailWord_2896086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896086).length < 2 ^ (prefixWord ++ tailWord_2896086).sum := by decide
  have hdescent : baseEnd_2896086 < baseStart_2896086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896112 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_2896112 : Nat := 118140960795 + 2896112 * 2 ^ 59
def prefixEnd_2896112 : Nat := 4983230072969 + 3 ^ 40 * 2896112 * 2
def baseEnd_2896112 : Nat := 495699161751359394060343

theorem tailTrace_2896112 : CollatzResearch.WordTrace tailWord_2896112 prefixEnd_2896112 495699161751359394060343 := by
  unfold tailWord_2896112
  simp only [CollatzResearch.WordTrace]
  refine ⟨52814941241944157698137295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70419921655925543597516393 52814941241944157698137295)
  ·
    refine ⟨79222411862916236547205943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52814941241944157698137295 79222411862916236547205943)
    ·
      refine ⟨118833617794374354820808915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79222411862916236547205943 118833617794374354820808915)
      ·
        refine ⟨178250426691561532231213373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118833617794374354820808915 178250426691561532231213373)
        ·
          refine ⟨66843910009335574586705015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178250426691561532231213373 66843910009335574586705015)
          ·
            refine ⟨100265865014003361880057523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66843910009335574586705015 100265865014003361880057523)
            ·
              refine ⟨150398797521005042820086285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100265865014003361880057523 150398797521005042820086285)
              ·
                refine ⟨56399549070376891057532357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150398797521005042820086285 56399549070376891057532357)
                ·
                  refine ⟨10574915450695667073287317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56399549070376891057532357 10574915450695667073287317)
                  ·
                    refine ⟨495699161751359394060343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10574915450695667073287317 495699161751359394060343)
                    ·
                      rfl

theorem cell23_2896112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_2896112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896112 prefixEnd_2896112 := by exact prefixLift 2896112
  have htrace : WordTrace (prefixWord ++ tailWord_2896112) baseStart_2896112 baseEnd_2896112 := by
    simpa [prefixWord, tailWord_2896112, baseEnd_2896112] using wordTrace_append hprefix tailTrace_2896112
  have hstable : (prefixWord ++ tailWord_2896112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896112).length < 2 ^ (prefixWord ++ tailWord_2896112).sum := by decide
  have hdescent : baseEnd_2896112 < baseStart_2896112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896119 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 8, 2]
def baseStart_2896119 : Nat := 118140960795 + 2896119 * 2 ^ 59
def prefixEnd_2896119 : Nat := 4983230072969 + 3 ^ 40 * 2896119 * 2
def baseEnd_2896119 : Nat := 1487101079618659654793497

theorem tailTrace_2896119 : CollatzResearch.WordTrace tailWord_2896119 prefixEnd_2896119 1487101079618659654793497 := by
  unfold tailWord_2896119
  simp only [CollatzResearch.WordTrace]
  refine ⟨105630137794862955591779411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70420091863241970394519607 105630137794862955591779411)
  ·
    refine ⟨158445206692294433387669117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105630137794862955591779411 158445206692294433387669117)
    ·
      refine ⟨59416952509610412520375919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158445206692294433387669117 59416952509610412520375919)
      ·
        refine ⟨89125428764415618780563879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59416952509610412520375919 89125428764415618780563879)
        ·
          refine ⟨133688143146623428170845819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89125428764415618780563879 133688143146623428170845819)
          ·
            refine ⟨200532214719935142256268729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133688143146623428170845819 200532214719935142256268729)
            ·
              refine ⟨150399161039951356692201547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200532214719935142256268729 150399161039951356692201547)
              ·
                refine ⟨225598741559927035038302321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150399161039951356692201547 225598741559927035038302321)
                ·
                  refine ⟨169199056169945276278726741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225598741559927035038302321 169199056169945276278726741)
                  ·
                    refine ⟨1982801439491546206391329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 169199056169945276278726741 1982801439491546206391329)
                    ·
                      refine ⟨1487101079618659654793497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982801439491546206391329 1487101079618659654793497)
                      ·
                        rfl

theorem cell23_2896119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_2896119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896119 prefixEnd_2896119 := by exact prefixLift 2896119
  have htrace : WordTrace (prefixWord ++ tailWord_2896119) baseStart_2896119 baseEnd_2896119 := by
    simpa [prefixWord, tailWord_2896119, baseEnd_2896119] using wordTrace_append hprefix tailTrace_2896119
  have hstable : (prefixWord ++ tailWord_2896119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896119).length < 2 ^ (prefixWord ++ tailWord_2896119).sum := by decide
  have hdescent : baseEnd_2896119 < baseStart_2896119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896130 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_2896130 : Nat := 118140960795 + 2896130 * 2 ^ 59
def prefixEnd_2896130 : Nat := 4983230072969 + 3 ^ 40 * 2896130 * 2
def baseEnd_2896130 : Nat := 1487106727905859111755947

theorem tailTrace_2896130 : CollatzResearch.WordTrace tailWord_2896130 prefixEnd_2896130 1487106727905859111755947 := by
  unfold tailWord_2896130
  simp only [CollatzResearch.WordTrace]
  refine ⟨26407634749455776117607461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70420359331882069646953229 26407634749455776117607461)
  ·
    refine ⟨4951431515522958022051399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26407634749455776117607461 4951431515522958022051399)
    ·
      refine ⟨7427147273284437033077099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951431515522958022051399 7427147273284437033077099)
      ·
        refine ⟨11140720909926655549615649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7427147273284437033077099 11140720909926655549615649)
        ·
          refine ⟨8355540682444991662211737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11140720909926655549615649 8355540682444991662211737)
          ·
            refine ⟨6266655511833743746658803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8355540682444991662211737 6266655511833743746658803)
            ·
              refine ⟨9399983267750615619988205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266655511833743746658803 9399983267750615619988205)
              ·
                refine ⟨3524993725406480857495577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9399983267750615619988205 3524993725406480857495577)
                ·
                  refine ⟨2643745294054860643121683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3524993725406480857495577 2643745294054860643121683)
                  ·
                    refine ⟨3965617941082290964682525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2643745294054860643121683 3965617941082290964682525)
                    ·
                      refine ⟨1487106727905859111755947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3965617941082290964682525 1487106727905859111755947)
                      ·
                        rfl

theorem cell23_2896130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_2896130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896130 prefixEnd_2896130 := by exact prefixLift 2896130
  have htrace : WordTrace (prefixWord ++ tailWord_2896130) baseStart_2896130 baseEnd_2896130 := by
    simpa [prefixWord, tailWord_2896130, baseEnd_2896130] using wordTrace_append hprefix tailTrace_2896130
  have hstable : (prefixWord ++ tailWord_2896130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896130).length < 2 ^ (prefixWord ++ tailWord_2896130).sum := by decide
  have hdescent : baseEnd_2896130 < baseStart_2896130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896157 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_2896157 : Nat := 118140960795 + 2896157 * 2 ^ 59
def prefixEnd_2896157 : Nat := 4983230072969 + 3 ^ 40 * 2896157 * 2
def baseEnd_2896157 : Nat := 1487120591883530506118323

theorem tailTrace_2896157 : CollatzResearch.WordTrace tailWord_2896157 prefixEnd_2896157 1487120591883530506118323 := by
  unfold tailWord_2896157
  simp only [CollatzResearch.WordTrace]
  refine ⟨105631523768725288081662725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70421015845816858721108483 105631523768725288081662725)
  ·
    refine ⟨19805910706635991515311761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105631523768725288081662725 19805910706635991515311761)
    ·
      refine ⟨14854433029976993636483821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19805910706635991515311761 14854433029976993636483821)
      ·
        refine ⟨5570412386241372613681433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14854433029976993636483821 5570412386241372613681433)
        ·
          refine ⟨4177809289681029460261075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5570412386241372613681433 4177809289681029460261075)
          ·
            refine ⟨6266713934521544190391613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4177809289681029460261075 6266713934521544190391613)
            ·
              refine ⟨2350017725445579071396855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6266713934521544190391613 2350017725445579071396855)
              ·
                refine ⟨3525026588168368607095283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350017725445579071396855 3525026588168368607095283)
                ·
                  refine ⟨5287539882252552910642925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525026588168368607095283 5287539882252552910642925)
                  ·
                    refine ⟨1982827455844707341491097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5287539882252552910642925 1982827455844707341491097)
                    ·
                      refine ⟨1487120591883530506118323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982827455844707341491097 1487120591883530506118323)
                      ·
                        rfl

theorem cell23_2896157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_2896157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896157 prefixEnd_2896157 := by exact prefixLift 2896157
  have htrace : WordTrace (prefixWord ++ tailWord_2896157) baseStart_2896157 baseEnd_2896157 := by
    simpa [prefixWord, tailWord_2896157, baseEnd_2896157] using wordTrace_append hprefix tailTrace_2896157
  have hstable : (prefixWord ++ tailWord_2896157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896157).length < 2 ^ (prefixWord ++ tailWord_2896157).sum := by decide
  have hdescent : baseEnd_2896157 < baseStart_2896157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896186 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_2896186 : Nat := 118140960795 + 2896186 * 2 ^ 59
def prefixEnd_2896186 : Nat := 4983230072969 + 3 ^ 40 * 2896186 * 2
def baseEnd_2896186 : Nat := 1487135482822510892655689

theorem tailTrace_2896186 : CollatzResearch.WordTrace tailWord_2896186 prefixEnd_2896186 1487135482822510892655689 := by
  unfold tailWord_2896186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26408145371405056508617103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70421720990413484022978941 26408145371405056508617103)
  ·
    refine ⟨39612218057107584762925655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26408145371405056508617103 39612218057107584762925655)
    ·
      refine ⟨59418327085661377144388483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39612218057107584762925655 59418327085661377144388483)
      ·
        refine ⟨89127490628492065716582725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59418327085661377144388483 89127490628492065716582725)
        ·
          refine ⟨16711404492842262321859261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89127490628492065716582725 16711404492842262321859261)
          ·
            refine ⟨6266776684815848370697223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16711404492842262321859261 6266776684815848370697223)
            ·
              refine ⟨9400165027223772556045835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266776684815848370697223 9400165027223772556045835)
              ·
                refine ⟨14100247540835658834068753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9400165027223772556045835 14100247540835658834068753)
                ·
                  refine ⟨10575185655626744125551565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14100247540835658834068753 10575185655626744125551565)
                  ·
                    refine ⟨3965694620860029047081837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10575185655626744125551565 3965694620860029047081837)
                    ·
                      refine ⟨1487135482822510892655689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3965694620860029047081837 1487135482822510892655689)
                      ·
                        rfl

theorem cell23_2896186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_2896186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896186 prefixEnd_2896186 := by exact prefixLift 2896186
  have htrace : WordTrace (prefixWord ++ tailWord_2896186) baseStart_2896186 baseEnd_2896186 := by
    simpa [prefixWord, tailWord_2896186, baseEnd_2896186] using wordTrace_append hprefix tailTrace_2896186
  have hstable : (prefixWord ++ tailWord_2896186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896186).length < 2 ^ (prefixWord ++ tailWord_2896186).sum := by decide
  have hdescent : baseEnd_2896186 < baseStart_2896186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896313 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 1, 5]
def baseStart_2896313 : Nat := 118140960795 + 2896313 * 2 ^ 59
def prefixEnd_2896313 : Nat := 4983230072969 + 3 ^ 40 * 2896313 * 2
def baseEnd_2896313 : Nat := 495733564955210631922535

theorem tailTrace_2896313 : CollatzResearch.WordTrace tailWord_2896313 prefixEnd_2896313 495733564955210631922535 := by
  unfold tailWord_2896313
  simp only [CollatzResearch.WordTrace]
  refine ⟨105637213556160126724341593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70424809037440084482894395 105637213556160126724341593)
  ·
    refine ⟨79227910167120095043256195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105637213556160126724341593 79227910167120095043256195)
    ·
      refine ⟨118841865250680142564884293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79227910167120095043256195 118841865250680142564884293)
      ·
        refine ⟨22282849734502526730915805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118841865250680142564884293 22282849734502526730915805)
        ·
          refine ⟨8356068650438447524093427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22282849734502526730915805 8356068650438447524093427)
          ·
            refine ⟨12534102975657671286140141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356068650438447524093427 12534102975657671286140141)
            ·
              refine ⟨4700288615871626732302553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12534102975657671286140141 4700288615871626732302553)
              ·
                refine ⟨3525216461903720049226915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4700288615871626732302553 3525216461903720049226915)
                ·
                  refine ⟨5287824692855580073840373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525216461903720049226915 5287824692855580073840373)
                  ·
                    refine ⟨495733564955210631922535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5287824692855580073840373 495733564955210631922535)
                    ·
                      rfl

theorem cell23_2896313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_2896313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896313 prefixEnd_2896313 := by exact prefixLift 2896313
  have htrace : WordTrace (prefixWord ++ tailWord_2896313) baseStart_2896313 baseEnd_2896313 := by
    simpa [prefixWord, tailWord_2896313, baseEnd_2896313] using wordTrace_append hprefix tailTrace_2896313
  have hstable : (prefixWord ++ tailWord_2896313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896313).length < 2 ^ (prefixWord ++ tailWord_2896313).sum := by decide
  have hdescent : baseEnd_2896313 < baseStart_2896313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896319 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_2896319 : Nat := 118140960795 + 2896319 * 2 ^ 59
def prefixEnd_2896319 : Nat := 4983230072969 + 3 ^ 40 * 2896319 * 2
def baseEnd_2896319 : Nat := 1487203775749558872292577

theorem tailTrace_2896319 : CollatzResearch.WordTrace tailWord_2896319 prefixEnd_2896319 1487203775749558872292577 := by
  unfold tailWord_2896319
  simp only [CollatzResearch.WordTrace]
  refine ⟨105637432394138389749060011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70424954929425593166040007 105637432394138389749060011)
  ·
    refine ⟨158456148591207584623590017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105637432394138389749060011 158456148591207584623590017)
    ·
      refine ⟨118842111443405688467692513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158456148591207584623590017 118842111443405688467692513)
      ·
        refine ⟨89131583582554266350769385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118842111443405688467692513 89131583582554266350769385)
        ·
          refine ⟨66848687686915699763077039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89131583582554266350769385 66848687686915699763077039)
          ·
            refine ⟨100273031530373549644615559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66848687686915699763077039 100273031530373549644615559)
            ·
              refine ⟨150409547295560324466923339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100273031530373549644615559 150409547295560324466923339)
              ·
                refine ⟨225614320943340486700385009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150409547295560324466923339 225614320943340486700385009)
                ·
                  refine ⟨169210740707505365025288757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225614320943340486700385009 169210740707505365025288757)
                  ·
                    refine ⟨15863506941328627971120821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169210740707505365025288757 15863506941328627971120821)
                    ·
                      refine ⟨1487203775749558872292577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15863506941328627971120821 1487203775749558872292577)
                      ·
                        rfl

theorem cell23_2896319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_2896319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896319 prefixEnd_2896319 := by exact prefixLift 2896319
  have htrace : WordTrace (prefixWord ++ tailWord_2896319) baseStart_2896319 baseEnd_2896319 := by
    simpa [prefixWord, tailWord_2896319, baseEnd_2896319] using wordTrace_append hprefix tailTrace_2896319
  have hstable : (prefixWord ++ tailWord_2896319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896319).length < 2 ^ (prefixWord ++ tailWord_2896319).sum := by decide
  have hdescent : baseEnd_2896319 < baseStart_2896319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896336 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_2896336 : Nat := 118140960795 + 2896336 * 2 ^ 59
def prefixEnd_2896336 : Nat := 4983230072969 + 3 ^ 40 * 2896336 * 2
def baseEnd_2896336 : Nat := 1487212504920685305779999

theorem tailTrace_2896336 : CollatzResearch.WordTrace tailWord_2896336 prefixEnd_2896336 1487212504920685305779999 := by
  unfold tailWord_2896336
  simp only [CollatzResearch.WordTrace]
  refine ⟨52819026217538400826214431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70425368290051201101619241 52819026217538400826214431)
  ·
    refine ⟨79228539326307601239321647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52819026217538400826214431 79228539326307601239321647)
    ·
      refine ⟨118842808989461401858982471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79228539326307601239321647 118842808989461401858982471)
      ·
        refine ⟨178264213484192102788473707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118842808989461401858982471 178264213484192102788473707)
        ·
          refine ⟨267396320226288154182710561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178264213484192102788473707 267396320226288154182710561)
          ·
            refine ⟨200547240169716115637032921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267396320226288154182710561 200547240169716115637032921)
            ·
              refine ⟨150410430127287086727774691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200547240169716115637032921 150410430127287086727774691)
              ·
                refine ⟨225615645190930630091662037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150410430127287086727774691 225615645190930630091662037)
                ·
                  refine ⟨5287866684162436642773329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 225615645190930630091662037 5287866684162436642773329)
                  ·
                    refine ⟨3965900013121827482079997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5287866684162436642773329 3965900013121827482079997)
                    ·
                      refine ⟨1487212504920685305779999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3965900013121827482079997 1487212504920685305779999)
                      ·
                        rfl

theorem cell23_2896336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_2896336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896336 prefixEnd_2896336 := by exact prefixLift 2896336
  have htrace : WordTrace (prefixWord ++ tailWord_2896336) baseStart_2896336 baseEnd_2896336 := by
    simpa [prefixWord, tailWord_2896336, baseEnd_2896336] using wordTrace_append hprefix tailTrace_2896336
  have hstable : (prefixWord ++ tailWord_2896336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896336).length < 2 ^ (prefixWord ++ tailWord_2896336).sum := by decide
  have hdescent : baseEnd_2896336 < baseStart_2896336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896346 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_2896346 : Nat := 118140960795 + 2896346 * 2 ^ 59
def prefixEnd_2896346 : Nat := 4983230072969 + 3 ^ 40 * 2896346 * 2
def baseEnd_2896346 : Nat := 1487217639727230266654953

theorem tailTrace_2896346 : CollatzResearch.WordTrace tailWord_2896346 prefixEnd_2896346 1487217639727230266654953 := by
  unfold tailWord_2896346
  simp only [CollatzResearch.WordTrace]
  refine ⟨26409604291260143340073223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70425611443360382240195261 26409604291260143340073223)
  ·
    refine ⟨39614406436890215010109835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26409604291260143340073223 39614406436890215010109835)
    ·
      refine ⟨59421609655335322515164753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39614406436890215010109835 59421609655335322515164753)
      ·
        refine ⟨44566207241501491886373565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59421609655335322515164753 44566207241501491886373565)
        ·
          refine ⟨16712327715563059457390087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44566207241501491886373565 16712327715563059457390087)
          ·
            refine ⟨25068491573344589186085131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16712327715563059457390087 25068491573344589186085131)
            ·
              refine ⟨37602737360016883779127697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25068491573344589186085131 37602737360016883779127697)
              ·
                refine ⟨28202053020012662834345773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37602737360016883779127697 28202053020012662834345773)
                ·
                  refine ⟨10575769882504748562879665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28202053020012662834345773 10575769882504748562879665)
                  ·
                    refine ⟨7931827411878561422159749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10575769882504748562879665 7931827411878561422159749)
                    ·
                      refine ⟨1487217639727230266654953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7931827411878561422159749 1487217639727230266654953)
                      ·
                        rfl

theorem cell23_2896346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_2896346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896346 prefixEnd_2896346 := by exact prefixLift 2896346
  have htrace : WordTrace (prefixWord ++ tailWord_2896346) baseStart_2896346 baseEnd_2896346 := by
    simpa [prefixWord, tailWord_2896346, baseEnd_2896346] using wordTrace_append hprefix tailTrace_2896346
  have hstable : (prefixWord ++ tailWord_2896346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896346).length < 2 ^ (prefixWord ++ tailWord_2896346).sum := by decide
  have hdescent : baseEnd_2896346 < baseStart_2896346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896383 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 3]
def baseStart_2896383 : Nat := 118140960795 + 2896383 * 2 ^ 59
def prefixEnd_2896383 : Nat := 4983230072969 + 3 ^ 40 * 2896383 * 2
def baseEnd_2896383 : Nat := 1487236638511446621892283

theorem tailTrace_2896383 : CollatzResearch.WordTrace tailWord_2896383 prefixEnd_2896383 1487236638511446621892283 := by
  unfold tailWord_2896383
  simp only [CollatzResearch.WordTrace]
  refine ⟨105639766665906528679389803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70426511110604352452926535 105639766665906528679389803)
  ·
    refine ⟨158459649998859793019084705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105639766665906528679389803 158459649998859793019084705)
    ·
      refine ⟨118844737499144844764313529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158459649998859793019084705 118844737499144844764313529)
      ·
        refine ⟨89133553124358633573235147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118844737499144844764313529 89133553124358633573235147)
        ·
          refine ⟨133700329686537950359852721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89133553124358633573235147 133700329686537950359852721)
          ·
            refine ⟨100275247264903462769889541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133700329686537950359852721 100275247264903462769889541)
            ·
              refine ⟨18801608862169399269354289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100275247264903462769889541 18801608862169399269354289)
              ·
                refine ⟨14101206646627049452015717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18801608862169399269354289 14101206646627049452015717)
                ·
                  refine ⟨2643976246242571772252947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14101206646627049452015717 2643976246242571772252947)
                  ·
                    refine ⟨3965964369363857658379421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2643976246242571772252947 3965964369363857658379421)
                    ·
                      refine ⟨1487236638511446621892283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3965964369363857658379421 1487236638511446621892283)
                      ·
                        rfl

theorem cell23_2896383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_2896383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896383 prefixEnd_2896383 := by exact prefixLift 2896383
  have htrace : WordTrace (prefixWord ++ tailWord_2896383) baseStart_2896383 baseEnd_2896383 := by
    simpa [prefixWord, tailWord_2896383, baseEnd_2896383] using wordTrace_append hprefix tailTrace_2896383
  have hstable : (prefixWord ++ tailWord_2896383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896383).length < 2 ^ (prefixWord ++ tailWord_2896383).sum := by decide
  have hdescent : baseEnd_2896383 < baseStart_2896383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896393 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 5, 3, 2]
def baseStart_2896393 : Nat := 118140960795 + 2896393 * 2 ^ 59
def prefixEnd_2896393 : Nat := 4983230072969 + 3 ^ 40 * 2896393 * 2
def baseEnd_2896393 : Nat := 1487241773317991582767237

theorem tailTrace_2896393 : CollatzResearch.WordTrace tailWord_2896393 prefixEnd_2896393 1487241773317991582767237 := by
  unfold tailWord_2896393
  simp only [CollatzResearch.WordTrace]
  refine ⟨105640131395870300387253833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70426754263913533591502555 105640131395870300387253833)
  ·
    refine ⟨79230098546902725290440375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105640131395870300387253833 79230098546902725290440375)
    ·
      refine ⟨118845147820354087935660563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79230098546902725290440375 118845147820354087935660563)
      ·
        refine ⟨178267721730531131903490845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118845147820354087935660563 178267721730531131903490845)
        ·
          refine ⟨66850395648949174463809067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178267721730531131903490845 66850395648949174463809067)
          ·
            refine ⟨100275593473423761695713601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66850395648949174463809067 100275593473423761695713601)
            ·
              refine ⟨75206695105067821271785201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100275593473423761695713601 75206695105067821271785201)
              ·
                refine ⟨56405021328800865953838901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75206695105067821271785201 56405021328800865953838901)
                ·
                  refine ⟨5287970749575081183172397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56405021328800865953838901 5287970749575081183172397)
                  ·
                    refine ⟨1982989031090655443689649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5287970749575081183172397 1982989031090655443689649)
                    ·
                      refine ⟨1487241773317991582767237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1982989031090655443689649 1487241773317991582767237)
                      ·
                        rfl

theorem cell23_2896393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 3, 2].length) (baseStart_2896393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896393 prefixEnd_2896393 := by exact prefixLift 2896393
  have htrace : WordTrace (prefixWord ++ tailWord_2896393) baseStart_2896393 baseEnd_2896393 := by
    simpa [prefixWord, tailWord_2896393, baseEnd_2896393] using wordTrace_append hprefix tailTrace_2896393
  have hstable : (prefixWord ++ tailWord_2896393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896393).length < 2 ^ (prefixWord ++ tailWord_2896393).sum := by decide
  have hdescent : baseEnd_2896393 < baseStart_2896393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896417 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2896417 : Nat := 118140960795 + 2896417 * 2 ^ 59
def prefixEnd_2896417 : Nat := 4983230072969 + 3 ^ 40 * 2896417 * 2
def baseEnd_2896417 : Nat := 1487254096853699488867127

theorem tailTrace_2896417 : CollatzResearch.WordTrace tailWord_2896417 prefixEnd_2896417 1487254096853699488867127 := by
  unfold tailWord_2896417
  simp only [CollatzResearch.WordTrace]
  refine ⟨105641006747783352486127505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70427337831855568324085003 105641006747783352486127505)
  ·
    refine ⟨79230755060837514364595629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105641006747783352486127505 79230755060837514364595629)
    ·
      refine ⟨29711533147814067886723361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79230755060837514364595629 29711533147814067886723361)
      ·
        refine ⟨22283649860860550915042521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29711533147814067886723361 22283649860860550915042521)
        ·
          refine ⟨16712737395645413186281891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22283649860860550915042521 16712737395645413186281891)
          ·
            refine ⟨25069106093468119779422837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16712737395645413186281891 25069106093468119779422837)
            ·
              refine ⟨2350228696262636229320891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25069106093468119779422837 2350228696262636229320891)
              ·
                refine ⟨3525343044393954343981337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350228696262636229320891 3525343044393954343981337)
                ·
                  refine ⟨2644007283295465757986003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3525343044393954343981337 2644007283295465757986003)
                  ·
                    refine ⟨3966010924943198636979005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644007283295465757986003 3966010924943198636979005)
                    ·
                      refine ⟨1487254096853699488867127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3966010924943198636979005 1487254096853699488867127)
                      ·
                        rfl

theorem cell23_2896417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2896417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896417 prefixEnd_2896417 := by exact prefixLift 2896417
  have htrace : WordTrace (prefixWord ++ tailWord_2896417) baseStart_2896417 baseEnd_2896417 := by
    simpa [prefixWord, tailWord_2896417, baseEnd_2896417] using wordTrace_append hprefix tailTrace_2896417
  have hstable : (prefixWord ++ tailWord_2896417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896417).length < 2 ^ (prefixWord ++ tailWord_2896417).sum := by decide
  have hdescent : baseEnd_2896417 < baseStart_2896417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896440 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 6, 2, 2]
def baseStart_2896440 : Nat := 118140960795 + 2896440 * 2 ^ 59
def prefixEnd_2896440 : Nat := 4983230072969 + 3 ^ 40 * 2896440 * 2
def baseEnd_2896440 : Nat := 1487265906908752898879521

theorem tailTrace_2896440 : CollatzResearch.WordTrace tailWord_2896440 prefixEnd_2896440 1487265906908752898879521 := by
  unfold tailWord_2896440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52820922813350013707107387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70427897084466684942809849 52820922813350013707107387)
  ·
    refine ⟨79231384220025020560661081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52820922813350013707107387 79231384220025020560661081)
    ·
      refine ⟨59423538165018765420495811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79231384220025020560661081 59423538165018765420495811)
      ·
        refine ⟨89135307247528148130743717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59423538165018765420495811 89135307247528148130743717)
        ·
          refine ⟨16712870108911527774514447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89135307247528148130743717 16712870108911527774514447)
          ·
            refine ⟨25069305163367291661771671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16712870108911527774514447 25069305163367291661771671)
            ·
              refine ⟨37603957745050937492657507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25069305163367291661771671 37603957745050937492657507)
              ·
                refine ⟨56405936617576406238986261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37603957745050937492657507 56405936617576406238986261)
                ·
                  refine ⟨2644028278948894042452481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56405936617576406238986261 2644028278948894042452481)
                  ·
                    refine ⟨1983021209211670531839361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2644028278948894042452481 1983021209211670531839361)
                    ·
                      refine ⟨1487265906908752898879521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1983021209211670531839361 1487265906908752898879521)
                      ·
                        rfl

theorem cell23_2896440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_2896440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896440 prefixEnd_2896440 := by exact prefixLift 2896440
  have htrace : WordTrace (prefixWord ++ tailWord_2896440) baseStart_2896440 baseEnd_2896440 := by
    simpa [prefixWord, tailWord_2896440, baseEnd_2896440] using wordTrace_append hprefix tailTrace_2896440
  have hstable : (prefixWord ++ tailWord_2896440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896440).length < 2 ^ (prefixWord ++ tailWord_2896440).sum := by decide
  have hdescent : baseEnd_2896440 < baseStart_2896440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896463 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 5]
def baseStart_2896463 : Nat := 118140960795 + 2896463 * 2 ^ 59
def prefixEnd_2896463 : Nat := 4983230072969 + 3 ^ 40 * 2896463 * 2
def baseEnd_2896463 : Nat := 165253079662645145432435

theorem tailTrace_2896463 : CollatzResearch.WordTrace tailWord_2896463 prefixEnd_2896463 165253079662645145432435 := by
  unfold tailWord_2896463
  simp only [CollatzResearch.WordTrace]
  refine ⟨105642684505616702342302043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70428456337077801561534695 105642684505616702342302043)
  ·
    refine ⟨158464026758425053513453065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105642684505616702342302043 158464026758425053513453065)
    ·
      refine ⟨118848020068818790135089799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158464026758425053513453065 118848020068818790135089799)
      ·
        refine ⟨178272030103228185202634699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118848020068818790135089799 178272030103228185202634699)
        ·
          refine ⟨267408045154842277803952049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178272030103228185202634699 267408045154842277803952049)
          ·
            refine ⟨200556033866131708352964037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267408045154842277803952049 200556033866131708352964037)
            ·
              refine ⟨37604256349899695316180757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200556033866131708352964037 37604256349899695316180757)
              ·
                refine ⟨1762699516401548217945973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37604256349899695316180757 1762699516401548217945973)
                ·
                  refine ⟨165253079662645145432435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1762699516401548217945973 165253079662645145432435)
                  ·
                    rfl

theorem cell23_2896463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 5].length) (baseStart_2896463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896463 prefixEnd_2896463 := by exact prefixLift 2896463
  have htrace : WordTrace (prefixWord ++ tailWord_2896463) baseStart_2896463 baseEnd_2896463 := by
    simpa [prefixWord, tailWord_2896463, baseEnd_2896463] using wordTrace_append hprefix tailTrace_2896463
  have hstable : (prefixWord ++ tailWord_2896463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896463).length < 2 ^ (prefixWord ++ tailWord_2896463).sum := by decide
  have hdescent : baseEnd_2896463 < baseStart_2896463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896506 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 8]
def baseStart_2896506 : Nat := 118140960795 + 2896506 * 2 ^ 59
def prefixEnd_2896506 : Nat := 4983230072969 + 3 ^ 40 * 2896506 * 2
def baseEnd_2896506 : Nat := 495766598877316546884739

theorem tailTrace_2896506 : CollatzResearch.WordTrace tailWord_2896506 prefixEnd_2896506 495766598877316546884739 := by
  unfold tailWord_2896506
  simp only [CollatzResearch.WordTrace]
  refine ⟨26411063211115230171529343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70429501896307280457411581 26411063211115230171529343)
  ·
    refine ⟨39616594816672845257294015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26411063211115230171529343 39616594816672845257294015)
    ·
      refine ⟨59424892225009267885941023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39616594816672845257294015 59424892225009267885941023)
      ·
        refine ⟨89137338337513901828911535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59424892225009267885941023 89137338337513901828911535)
        ·
          refine ⟨133706007506270852743367303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89137338337513901828911535 133706007506270852743367303)
          ·
            refine ⟨200559011259406279115050955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133706007506270852743367303 200559011259406279115050955)
            ·
              refine ⟨300838516889109418672576433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200559011259406279115050955 300838516889109418672576433)
              ·
                refine ⟨225628887666832064004432325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300838516889109418672576433 225628887666832064004432325)
                ·
                  refine ⟨42305416437531012000831061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 225628887666832064004432325 42305416437531012000831061)
                  ·
                    refine ⟨495766598877316546884739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42305416437531012000831061 495766598877316546884739)
                    ·
                      rfl

theorem cell23_2896506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_2896506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896506 prefixEnd_2896506 := by exact prefixLift 2896506
  have htrace : WordTrace (prefixWord ++ tailWord_2896506) baseStart_2896506 baseEnd_2896506 := by
    simpa [prefixWord, tailWord_2896506, baseEnd_2896506] using wordTrace_append hprefix tailTrace_2896506
  have hstable : (prefixWord ++ tailWord_2896506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896506).length < 2 ^ (prefixWord ++ tailWord_2896506).sum := by decide
  have hdescent : baseEnd_2896506 < baseStart_2896506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896540 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2896540 : Nat := 118140960795 + 2896540 * 2 ^ 59
def prefixEnd_2896540 : Nat := 4983230072969 + 3 ^ 40 * 2896540 * 2
def baseEnd_2896540 : Nat := 495772418324734169209687

theorem tailTrace_2896540 : CollatzResearch.WordTrace tailWord_2896540 prefixEnd_2896540 495772418324734169209687 := by
  unfold tailWord_2896540
  simp only [CollatzResearch.WordTrace]
  refine ⟨52822746463168872246427537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70430328617558496328570049 52822746463168872246427537)
  ·
    refine ⟨39617059847376654184820653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52822746463168872246427537 39617059847376654184820653)
    ·
      refine ⟨14856397442766245319307745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39617059847376654184820653 14856397442766245319307745)
      ·
        refine ⟨11142298082074683989480809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14856397442766245319307745 11142298082074683989480809)
        ·
          refine ⟨8356723561556012992110607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11142298082074683989480809 8356723561556012992110607)
          ·
            refine ⟨12535085342334019488165911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356723561556012992110607 12535085342334019488165911)
            ·
              refine ⟨18802628013501029232248867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535085342334019488165911 18802628013501029232248867)
              ·
                refine ⟨28203942020251543848373301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18802628013501029232248867 28203942020251543848373301)
                ·
                  refine ⟨2644119564398582235784997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28203942020251543848373301 2644119564398582235784997)
                  ·
                    refine ⟨495772418324734169209687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2644119564398582235784997 495772418324734169209687)
                    ·
                      rfl

theorem cell23_2896540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2896540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896540 prefixEnd_2896540 := by exact prefixLift 2896540
  have htrace : WordTrace (prefixWord ++ tailWord_2896540) baseStart_2896540 baseEnd_2896540 := by
    simpa [prefixWord, tailWord_2896540, baseEnd_2896540] using wordTrace_append hprefix tailTrace_2896540
  have hstable : (prefixWord ++ tailWord_2896540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896540).length < 2 ^ (prefixWord ++ tailWord_2896540).sum := by decide
  have hdescent : baseEnd_2896540 < baseStart_2896540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896573 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2896573 : Nat := 118140960795 + 2896573 * 2 ^ 59
def prefixEnd_2896573 : Nat := 4983230072969 + 3 ^ 40 * 2896573 * 2
def baseEnd_2896573 : Nat := 1487334199835800878516409

theorem tailTrace_2896573 : CollatzResearch.WordTrace tailWord_2896573 prefixEnd_2896573 1487334199835800878516409 := by
  unfold tailWord_2896573
  simp only [CollatzResearch.WordTrace]
  refine ⟨105646696535218191128806373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70431131023478794085870915 105646696535218191128806373)
  ·
    refine ⟨19808755600353410836651195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105646696535218191128806373 19808755600353410836651195)
    ·
      refine ⟨29713133400530116254976793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19808755600353410836651195 29713133400530116254976793)
      ·
        refine ⟨22284850050397587191232595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29713133400530116254976793 22284850050397587191232595)
        ·
          refine ⟨33427275075596380786848893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22284850050397587191232595 33427275075596380786848893)
          ·
            refine ⟨12535228153348642795068335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33427275075596380786848893 12535228153348642795068335)
            ·
              refine ⟨18802842230022964192602503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535228153348642795068335 18802842230022964192602503)
              ·
                refine ⟨28204263345034446288903755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18802842230022964192602503 28204263345034446288903755)
                ·
                  refine ⟨42306395017551669433355633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28204263345034446288903755 42306395017551669433355633)
                  ·
                    refine ⟨31729796263163752075016725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42306395017551669433355633 31729796263163752075016725)
                    ·
                      refine ⟨1487334199835800878516409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31729796263163752075016725 1487334199835800878516409)
                      ·
                        rfl

theorem cell23_2896573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2896573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896573 prefixEnd_2896573 := by exact prefixLift 2896573
  have htrace : WordTrace (prefixWord ++ tailWord_2896573) baseStart_2896573 baseEnd_2896573 := by
    simpa [prefixWord, tailWord_2896573, baseEnd_2896573] using wordTrace_append hprefix tailTrace_2896573
  have hstable : (prefixWord ++ tailWord_2896573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896573).length < 2 ^ (prefixWord ++ tailWord_2896573).sum := by decide
  have hdescent : baseEnd_2896573 < baseStart_2896573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896583 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 3, 5]
def baseStart_2896583 : Nat := 118140960795 + 2896583 * 2 ^ 59
def prefixEnd_2896583 : Nat := 4983230072969 + 3 ^ 40 * 2896583 * 2
def baseEnd_2896583 : Nat := 495779778214115279797121

theorem tailTrace_2896583 : CollatzResearch.WordTrace tailWord_2896583 prefixEnd_2896583 495779778214115279797121 := by
  unfold tailWord_2896583
  simp only [CollatzResearch.WordTrace]
  refine ⟨105647061265181962836670403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70431374176787975224446935 105647061265181962836670403)
  ·
    refine ⟨158470591897772944255005605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105647061265181962836670403 158470591897772944255005605)
    ·
      refine ⟨29713235980832427047813551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158470591897772944255005605 29713235980832427047813551)
      ·
        refine ⟨44569853971248640571720327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29713235980832427047813551 44569853971248640571720327)
        ·
          refine ⟨66854780956872960857580491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44569853971248640571720327 66854780956872960857580491)
          ·
            refine ⟨100282171435309441286370737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66854780956872960857580491 100282171435309441286370737)
            ·
              refine ⟨75211628576482080964778053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100282171435309441286370737 75211628576482080964778053)
              ·
                refine ⟨14102180358090390180895885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75211628576482080964778053 14102180358090390180895885)
                ·
                  refine ⟨5288317634283896317835957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14102180358090390180895885 5288317634283896317835957)
                  ·
                    refine ⟨495779778214115279797121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5288317634283896317835957 495779778214115279797121)
                    ·
                      rfl

theorem cell23_2896583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_2896583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896583 prefixEnd_2896583 := by exact prefixLift 2896583
  have htrace : WordTrace (prefixWord ++ tailWord_2896583) baseStart_2896583 baseEnd_2896583 := by
    simpa [prefixWord, tailWord_2896583, baseEnd_2896583] using wordTrace_append hprefix tailTrace_2896583
  have hstable : (prefixWord ++ tailWord_2896583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896583).length < 2 ^ (prefixWord ++ tailWord_2896583).sum := by decide
  have hdescent : baseEnd_2896583 < baseStart_2896583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896600 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 1, 5]
def baseStart_2896600 : Nat := 118140960795 + 2896600 * 2 ^ 59
def prefixEnd_2896600 : Nat := 4983230072969 + 3 ^ 40 * 2896600 * 2
def baseEnd_2896600 : Nat := 495782687937824090959595

theorem tailTrace_2896600 : CollatzResearch.WordTrace tailWord_2896600 prefixEnd_2896600 495782687937824090959595 := by
  unfold tailWord_2896600
  simp only [CollatzResearch.WordTrace]
  refine ⟨52823840653060187370019627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70431787537413583160026169 52823840653060187370019627)
  ·
    refine ⟨79235760979590281055029441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52823840653060187370019627 79235760979590281055029441)
    ·
      refine ⟨59426820734692710791272081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79235760979590281055029441 59426820734692710791272081)
      ·
        refine ⟨44570115551019533093454061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59426820734692710791272081 44570115551019533093454061)
        ·
          refine ⟨16713793331632324910045273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44570115551019533093454061 16713793331632324910045273)
          ·
            refine ⟨12535344998724243682533955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16713793331632324910045273 12535344998724243682533955)
            ·
              refine ⟨18803017498086365523800933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535344998724243682533955 18803017498086365523800933)
              ·
                refine ⟨3525565780891193535712675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18803017498086365523800933 3525565780891193535712675)
                ·
                  refine ⟨5288348671336790303569013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525565780891193535712675 5288348671336790303569013)
                  ·
                    refine ⟨495782687937824090959595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5288348671336790303569013 495782687937824090959595)
                    ·
                      rfl

theorem cell23_2896600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_2896600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896600 prefixEnd_2896600 := by exact prefixLift 2896600
  have htrace : WordTrace (prefixWord ++ tailWord_2896600) baseStart_2896600 baseEnd_2896600 := by
    simpa [prefixWord, tailWord_2896600, baseEnd_2896600] using wordTrace_append hprefix tailTrace_2896600
  have hstable : (prefixWord ++ tailWord_2896600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896600).length < 2 ^ (prefixWord ++ tailWord_2896600).sum := by decide
  have hdescent : baseEnd_2896600 < baseStart_2896600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896650 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2896650 : Nat := 118140960795 + 2896650 * 2 ^ 59
def prefixEnd_2896650 : Nat := 4983230072969 + 3 ^ 40 * 2896650 * 2
def baseEnd_2896650 : Nat := 1487373737846197077253555

theorem tailTrace_2896650 : CollatzResearch.WordTrace tailWord_2896650 prefixEnd_2896650 1487373737846197077253555 := by
  unfold tailWord_2896650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412376238984808319839851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70433003303959488852906269 26412376238984808319839851)
  ·
    refine ⟨39618564358477212479759777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412376238984808319839851 39618564358477212479759777)
    ·
      refine ⟨29713923268857909359819833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39618564358477212479759777 29713923268857909359819833)
      ·
        refine ⟨22285442451643432019864875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29713923268857909359819833 22285442451643432019864875)
        ·
          refine ⟨33428163677465148029797313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22285442451643432019864875 33428163677465148029797313)
          ·
            refine ⟨25071122758098861022347985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33428163677465148029797313 25071122758098861022347985)
            ·
              refine ⟨18803342068574145766760989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25071122758098861022347985 18803342068574145766760989)
              ·
                refine ⟨7051253275715304662535371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18803342068574145766760989 7051253275715304662535371)
                ·
                  refine ⟨10576879913572956993803057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7051253275715304662535371 10576879913572956993803057)
                  ·
                    refine ⟨7932659935179717745352293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10576879913572956993803057 7932659935179717745352293)
                    ·
                      refine ⟨1487373737846197077253555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7932659935179717745352293 1487373737846197077253555)
                      ·
                        rfl

theorem cell23_2896650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2896650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896650 prefixEnd_2896650 := by exact prefixLift 2896650
  have htrace : WordTrace (prefixWord ++ tailWord_2896650) baseStart_2896650 baseEnd_2896650 := by
    simpa [prefixWord, tailWord_2896650, baseEnd_2896650] using wordTrace_append hprefix tailTrace_2896650
  have hstable : (prefixWord ++ tailWord_2896650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896650).length < 2 ^ (prefixWord ++ tailWord_2896650).sum := by decide
  have hdescent : baseEnd_2896650 < baseStart_2896650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896657 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_2896657 : Nat := 118140960795 + 2896657 * 2 ^ 59
def prefixEnd_2896657 : Nat := 4983230072969 + 3 ^ 40 * 2896657 * 2
def baseEnd_2896657 : Nat := 1487377332210778549866023

theorem tailTrace_2896657 : CollatzResearch.WordTrace tailWord_2896657 prefixEnd_2896657 1487377332210778549866023 := by
  unfold tailWord_2896657
  simp only [CollatzResearch.WordTrace]
  refine ⟨105649760266913873474864225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70433173511275915649909483 105649760266913873474864225)
  ·
    refine ⟨79237320200185405106148169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105649760266913873474864225 79237320200185405106148169)
    ·
      refine ⟨59427990150139053829611127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79237320200185405106148169 59427990150139053829611127)
      ·
        refine ⟨89141985225208580744416691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59427990150139053829611127 89141985225208580744416691)
        ·
          refine ⟨133712977837812871116625037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89141985225208580744416691 133712977837812871116625037)
          ·
            refine ⟨50142366689179826668734389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133712977837812871116625037 50142366689179826668734389)
            ·
              refine ⟨4700846877110608750193849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50142366689179826668734389 4700846877110608750193849)
              ·
                refine ⟨3525635157832956562645387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4700846877110608750193849 3525635157832956562645387)
                ·
                  refine ⟨5288452736749434843968081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525635157832956562645387 5288452736749434843968081)
                  ·
                    refine ⟨3966339552562076132976061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5288452736749434843968081 3966339552562076132976061)
                    ·
                      refine ⟨1487377332210778549866023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3966339552562076132976061 1487377332210778549866023)
                      ·
                        rfl

theorem cell23_2896657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_2896657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896657 prefixEnd_2896657 := by exact prefixLift 2896657
  have htrace : WordTrace (prefixWord ++ tailWord_2896657) baseStart_2896657 baseEnd_2896657 := by
    simpa [prefixWord, tailWord_2896657, baseEnd_2896657] using wordTrace_append hprefix tailTrace_2896657
  have hstable : (prefixWord ++ tailWord_2896657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896657).length < 2 ^ (prefixWord ++ tailWord_2896657).sum := by decide
  have hdescent : baseEnd_2896657 < baseStart_2896657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896682 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2896682 : Nat := 118140960795 + 2896682 * 2 ^ 59
def prefixEnd_2896682 : Nat := 4983230072969 + 3 ^ 40 * 2896682 * 2
def baseEnd_2896682 : Nat := 1487390169227140952053409

theorem tailTrace_2896682 : CollatzResearch.WordTrace tailWord_2896682 prefixEnd_2896682 1487390169227140952053409 := by
  unfold tailWord_2896682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412668022955825686131075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70433781394548868496349533 26412668022955825686131075)
  ·
    refine ⟨39619002034433738529196613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412668022955825686131075 39619002034433738529196613)
    ·
      refine ⟨7428562881456325974224365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39619002034433738529196613 7428562881456325974224365)
      ·
        refine ⟨2785711080546122240334137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7428562881456325974224365 2785711080546122240334137)
        ·
          refine ⟨2089283310409591680250603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2785711080546122240334137 2089283310409591680250603)
          ·
            refine ⟨3133924965614387520375905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089283310409591680250603 3133924965614387520375905)
            ·
              refine ⟨2350443724210790640281929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3133924965614387520375905 2350443724210790640281929)
              ·
                refine ⟨1762832793158092980211447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350443724210790640281929 1762832793158092980211447)
                ·
                  refine ⟨2644249189737139470317171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762832793158092980211447 2644249189737139470317171)
                  ·
                    refine ⟨3966373784605709205475757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644249189737139470317171 3966373784605709205475757)
                    ·
                      refine ⟨1487390169227140952053409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3966373784605709205475757 1487390169227140952053409)
                      ·
                        rfl

theorem cell23_2896682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2896682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896682 prefixEnd_2896682 := by exact prefixLift 2896682
  have htrace : WordTrace (prefixWord ++ tailWord_2896682) baseStart_2896682 baseEnd_2896682 := by
    simpa [prefixWord, tailWord_2896682, baseEnd_2896682] using wordTrace_append hprefix tailTrace_2896682
  have hstable : (prefixWord ++ tailWord_2896682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896682).length < 2 ^ (prefixWord ++ tailWord_2896682).sum := by decide
  have hdescent : baseEnd_2896682 < baseStart_2896682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896683 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_2896683 : Nat := 118140960795 + 2896683 * 2 ^ 59
def prefixEnd_2896683 : Nat := 4983230072969 + 3 ^ 40 * 2896683 * 2
def baseEnd_2896683 : Nat := 1487390682707795448140903

theorem tailTrace_2896683 : CollatzResearch.WordTrace tailWord_2896683 prefixEnd_2896683 1487390682707795448140903 := by
  unfold tailWord_2896683
  simp only [CollatzResearch.WordTrace]
  refine ⟨105650708564819679915310703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70433805709879786610207135 105650708564819679915310703)
  ·
    refine ⟨158476062847229519872966055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105650708564819679915310703 158476062847229519872966055)
    ·
      refine ⟨237714094270844279809449083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158476062847229519872966055 237714094270844279809449083)
      ·
        refine ⟨356571141406266419714173625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237714094270844279809449083 356571141406266419714173625)
        ·
          refine ⟨267428356054699814785630219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356571141406266419714173625 267428356054699814785630219)
          ·
            refine ⟨401142534082049722178445329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267428356054699814785630219 401142534082049722178445329)
            ·
              refine ⟨300856900561537291633833997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401142534082049722178445329 300856900561537291633833997)
              ·
                refine ⟨112821337710576484362687749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300856900561537291633833997 112821337710576484362687749)
                ·
                  refine ⟨21154000820733090818003953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112821337710576484362687749 21154000820733090818003953)
                  ·
                    refine ⟨15865500615549818113502965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21154000820733090818003953 15865500615549818113502965)
                    ·
                      refine ⟨1487390682707795448140903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15865500615549818113502965 1487390682707795448140903)
                      ·
                        rfl

theorem cell23_2896683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_2896683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896683 prefixEnd_2896683 := by exact prefixLift 2896683
  have htrace : WordTrace (prefixWord ++ tailWord_2896683) baseStart_2896683 baseEnd_2896683 := by
    simpa [prefixWord, tailWord_2896683, baseEnd_2896683] using wordTrace_append hprefix tailTrace_2896683
  have hstable : (prefixWord ++ tailWord_2896683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896683).length < 2 ^ (prefixWord ++ tailWord_2896683).sum := by decide
  have hdescent : baseEnd_2896683 < baseStart_2896683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896694 : List Nat := [5, 1, 2, 2, 2, 2, 1, 8]
def baseStart_2896694 : Nat := 118140960795 + 2896694 * 2 ^ 59
def prefixEnd_2896694 : Nat := 4983230072969 + 3 ^ 40 * 2896694 * 2
def baseEnd_2896694 : Nat := 55088752999814626114939

theorem tailTrace_2896694 : CollatzResearch.WordTrace tailWord_2896694 prefixEnd_2896694 55088752999814626114939 := by
  unfold tailWord_2896694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603194360486239299622571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70434073178519885862640757 6603194360486239299622571)
  ·
    refine ⟨9904791540729358949433857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6603194360486239299622571 9904791540729358949433857)
    ·
      refine ⟨7428593655547019212075393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9904791540729358949433857 7428593655547019212075393)
      ·
        refine ⟨5571445241660264409056545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7428593655547019212075393 5571445241660264409056545)
        ·
          refine ⟨4178583931245198306792409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5571445241660264409056545 4178583931245198306792409)
          ·
            refine ⟨3133937948433898730094307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178583931245198306792409 3133937948433898730094307)
            ·
              refine ⟨4700906922650848095141461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133937948433898730094307 4700906922650848095141461)
              ·
                refine ⟨55088752999814626114939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4700906922650848095141461 55088752999814626114939)
                ·
                  rfl

theorem cell23_2896694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_2896694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896694 prefixEnd_2896694 := by exact prefixLift 2896694
  have htrace : WordTrace (prefixWord ++ tailWord_2896694) baseStart_2896694 baseEnd_2896694 := by
    simpa [prefixWord, tailWord_2896694, baseEnd_2896694] using wordTrace_append hprefix tailTrace_2896694
  have hstable : (prefixWord ++ tailWord_2896694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896694).length < 2 ^ (prefixWord ++ tailWord_2896694).sum := by decide
  have hdescent : baseEnd_2896694 < baseStart_2896694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896738 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2896738 : Nat := 118140960795 + 2896738 * 2 ^ 59
def prefixEnd_2896738 : Nat := 4983230072969 + 3 ^ 40 * 2896738 * 2
def baseEnd_2896738 : Nat := 1487418924143792732953151

theorem tailTrace_2896738 : CollatzResearch.WordTrace tailWord_2896738 prefixEnd_2896738 1487418924143792732953151 := by
  unfold tailWord_2896738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413178644905106077140717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70435143053080282872375245 26413178644905106077140717)
  ·
    refine ⟨9904941991839414778927769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26413178644905106077140717 9904941991839414778927769)
    ·
      refine ⟨7428706493879561084195827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9904941991839414778927769 7428706493879561084195827)
      ·
        refine ⟨11143059740819341626293741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428706493879561084195827 11143059740819341626293741)
        ·
          refine ⟨4178647402807253109860153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11143059740819341626293741 4178647402807253109860153)
          ·
            refine ⟨3133985552105439832395115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178647402807253109860153 3133985552105439832395115)
            ·
              refine ⟨4700978328158159748592673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133985552105439832395115 4700978328158159748592673)
              ·
                refine ⟨3525733746118619811444505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4700978328158159748592673 3525733746118619811444505)
                ·
                  refine ⟨2644300309588964858583379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3525733746118619811444505 2644300309588964858583379)
                  ·
                    refine ⟨3966450464383447287875069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644300309588964858583379 3966450464383447287875069)
                    ·
                      refine ⟨1487418924143792732953151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3966450464383447287875069 1487418924143792732953151)
                      ·
                        rfl

theorem cell23_2896738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2896738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896738 prefixEnd_2896738 := by exact prefixLift 2896738
  have htrace : WordTrace (prefixWord ++ tailWord_2896738) baseStart_2896738 baseEnd_2896738 := by
    simpa [prefixWord, tailWord_2896738, baseEnd_2896738] using wordTrace_append hprefix tailTrace_2896738
  have hstable : (prefixWord ++ tailWord_2896738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896738).length < 2 ^ (prefixWord ++ tailWord_2896738).sum := by decide
  have hdescent : baseEnd_2896738 < baseStart_2896738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896757 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2896757 : Nat := 118140960795 + 2896757 * 2 ^ 59
def prefixEnd_2896757 : Nat := 4983230072969 + 3 ^ 40 * 2896757 * 2
def baseEnd_2896757 : Nat := 1487428680276228158615563

theorem tailTrace_2896757 : CollatzResearch.WordTrace tailWord_2896757 prefixEnd_2896757 1487428680276228158615563 := by
  unfold tailWord_2896757
  simp only [CollatzResearch.WordTrace]
  refine ⟨105653407566551590553504525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70435605044367727035669683 105653407566551590553504525)
  ·
    refine ⟨39620027837456846457564197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105653407566551590553504525 39620027837456846457564197)
    ·
      refine ⟨7428755219523158710793287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39620027837456846457564197 7428755219523158710793287)
      ·
        refine ⟨11143132829284738066189931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428755219523158710793287 11143132829284738066189931)
        ·
          refine ⟨16714699243927107099284897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11143132829284738066189931 16714699243927107099284897)
          ·
            refine ⟨12536024432945330324463673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16714699243927107099284897 12536024432945330324463673)
            ·
              refine ⟨9402018324708997743347755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12536024432945330324463673 9402018324708997743347755)
              ·
                refine ⟨14103027487063496615021633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402018324708997743347755 14103027487063496615021633)
                ·
                  refine ⟨10577270615297622461266225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14103027487063496615021633 10577270615297622461266225)
                  ·
                    refine ⟨7932952961473216845949669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10577270615297622461266225 7932952961473216845949669)
                    ·
                      refine ⟨1487428680276228158615563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7932952961473216845949669 1487428680276228158615563)
                      ·
                        rfl

theorem cell23_2896757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2896757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896757 prefixEnd_2896757 := by exact prefixLift 2896757
  have htrace : WordTrace (prefixWord ++ tailWord_2896757) baseStart_2896757 baseEnd_2896757 := by
    simpa [prefixWord, tailWord_2896757, baseEnd_2896757] using wordTrace_append hprefix tailTrace_2896757
  have hstable : (prefixWord ++ tailWord_2896757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896757).length < 2 ^ (prefixWord ++ tailWord_2896757).sum := by decide
  have hdescent : baseEnd_2896757 < baseStart_2896757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896760 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_2896760 : Nat := 118140960795 + 2896760 * 2 ^ 59
def prefixEnd_2896760 : Nat := 4983230072969 + 3 ^ 40 * 2896760 * 2
def baseEnd_2896760 : Nat := 1487430220718191646878049

theorem tailTrace_2896760 : CollatzResearch.WordTrace tailWord_2896760 prefixEnd_2896760 1487430220718191646878049 := by
  unfold tailWord_2896760
  simp only [CollatzResearch.WordTrace]
  refine ⟨52826758492770361032931867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70435677990360481377242489 52826758492770361032931867)
  ·
    refine ⟨79240137739155541549397801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52826758492770361032931867 79240137739155541549397801)
    ·
      refine ⟨59430103304366656162048351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79240137739155541549397801 59430103304366656162048351)
      ·
        refine ⟨89145154956549984243072527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59430103304366656162048351 89145154956549984243072527)
        ·
          refine ⟨133717732434824976364608791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89145154956549984243072527 133717732434824976364608791)
          ·
            refine ⟨200576598652237464546913187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133717732434824976364608791 200576598652237464546913187)
            ·
              refine ⟨300864897978356196820369781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200576598652237464546913187 300864897978356196820369781)
              ·
                refine ⟨28206084185470893451909667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 300864897978356196820369781 28206084185470893451909667)
                ·
                  refine ⟨42309126278206340177864501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28206084185470893451909667 42309126278206340177864501)
                  ·
                    refine ⟨3966480588581844391674797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42309126278206340177864501 3966480588581844391674797)
                    ·
                      refine ⟨1487430220718191646878049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3966480588581844391674797 1487430220718191646878049)
                      ·
                        rfl

theorem cell23_2896760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_2896760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896760 prefixEnd_2896760 := by exact prefixLift 2896760
  have htrace : WordTrace (prefixWord ++ tailWord_2896760) baseStart_2896760 baseEnd_2896760 := by
    simpa [prefixWord, tailWord_2896760, baseEnd_2896760] using wordTrace_append hprefix tailTrace_2896760
  have hstable : (prefixWord ++ tailWord_2896760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896760).length < 2 ^ (prefixWord ++ tailWord_2896760).sum := by decide
  have hdescent : baseEnd_2896760 < baseStart_2896760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896780 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_2896780 : Nat := 118140960795 + 2896780 * 2 ^ 59
def prefixEnd_2896780 : Nat := 4983230072969 + 3 ^ 40 * 2896780 * 2
def baseEnd_2896780 : Nat := 495813496777093856209319

theorem tailTrace_2896780 : CollatzResearch.WordTrace tailWord_2896780 prefixEnd_2896780 495813496777093856209319 := by
  unfold tailWord_2896780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52827123222734132740795897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70436164296978843654394529 52827123222734132740795897)
  ·
    refine ⟨39620342417050599555596923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52827123222734132740795897 39620342417050599555596923)
    ·
      refine ⟨59430513625575899333395385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39620342417050599555596923 59430513625575899333395385)
      ·
        refine ⟨44572885219181924500046539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59430513625575899333395385 44572885219181924500046539)
        ·
          refine ⟨66859327828772886750069809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44572885219181924500046539 66859327828772886750069809)
          ·
            refine ⟨50144495871579665062552357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66859327828772886750069809 50144495871579665062552357)
            ·
              refine ⟨9402092975921187199228567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50144495871579665062552357 9402092975921187199228567)
              ·
                refine ⟨14103139463881780798842851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402092975921187199228567 14103139463881780798842851)
                ·
                  refine ⟨21154709195822671198264277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14103139463881780798842851 21154709195822671198264277)
                  ·
                    refine ⟨495813496777093856209319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21154709195822671198264277 495813496777093856209319)
                    ·
                      rfl

theorem cell23_2896780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_2896780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896780 prefixEnd_2896780 := by exact prefixLift 2896780
  have htrace : WordTrace (prefixWord ++ tailWord_2896780) baseStart_2896780 baseEnd_2896780 := by
    simpa [prefixWord, tailWord_2896780, baseEnd_2896780] using wordTrace_append hprefix tailTrace_2896780
  have hstable : (prefixWord ++ tailWord_2896780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896780).length < 2 ^ (prefixWord ++ tailWord_2896780).sum := by decide
  have hdescent : baseEnd_2896780 < baseStart_2896780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896797 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2896797 : Nat := 118140960795 + 2896797 * 2 ^ 59
def prefixEnd_2896797 : Nat := 4983230072969 + 3 ^ 40 * 2896797 * 2
def baseEnd_2896797 : Nat := 495816406500802667371793

theorem tailTrace_2896797 : CollatzResearch.WordTrace tailWord_2896797 prefixEnd_2896797 495816406500802667371793 := by
  unfold tailWord_2896797
  simp only [CollatzResearch.WordTrace]
  refine ⟨105654866486406677384960645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70436577657604451589973763 105654866486406677384960645)
  ·
    refine ⟨19810287466201252009680121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105654866486406677384960645 19810287466201252009680121)
    ·
      refine ⟨14857715599650939007260091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19810287466201252009680121 14857715599650939007260091)
      ·
        refine ⟨22286573399476408510890137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14857715599650939007260091 22286573399476408510890137)
        ·
          refine ⟨16714930049607306383167603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22286573399476408510890137 16714930049607306383167603)
          ·
            refine ⟨25072395074410959574751405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16714930049607306383167603 25072395074410959574751405)
            ·
              refine ⟨9402148152904109840531777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25072395074410959574751405 9402148152904109840531777)
              ·
                refine ⟨7051611114678082380398833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9402148152904109840531777 7051611114678082380398833)
                ·
                  refine ⟨5288708336008561785299125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7051611114678082380398833 5288708336008561785299125)
                  ·
                    refine ⟨495816406500802667371793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5288708336008561785299125 495816406500802667371793)
                    ·
                      rfl

theorem cell23_2896797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2896797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896797 prefixEnd_2896797 := by exact prefixLift 2896797
  have htrace : WordTrace (prefixWord ++ tailWord_2896797) baseStart_2896797 baseEnd_2896797 := by
    simpa [prefixWord, tailWord_2896797, baseEnd_2896797] using wordTrace_append hprefix tailTrace_2896797
  have hstable : (prefixWord ++ tailWord_2896797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896797).length < 2 ^ (prefixWord ++ tailWord_2896797).sum := by decide
  have hdescent : baseEnd_2896797 < baseStart_2896797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896801 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 5]
def baseStart_2896801 : Nat := 118140960795 + 2896801 * 2 ^ 59
def prefixEnd_2896801 : Nat := 4983230072969 + 3 ^ 40 * 2896801 * 2
def baseEnd_2896801 : Nat := 165272363713891776273929

theorem tailTrace_2896801 : CollatzResearch.WordTrace tailWord_2896801 prefixEnd_2896801 165272363713891776273929 := by
  unfold tailWord_2896801
  simp only [CollatzResearch.WordTrace]
  refine ⟨105655012378392186068106257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70436674918928124045404171 105655012378392186068106257)
  ·
    refine ⟨79241259283794139551079693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105655012378392186068106257 79241259283794139551079693)
    ·
      refine ⟨29715472231422802331654885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79241259283794139551079693 29715472231422802331654885)
      ·
        refine ⟨5571651043391775437185291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29715472231422802331654885 5571651043391775437185291)
        ·
          refine ⟨8357476565087663155777937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571651043391775437185291 8357476565087663155777937)
          ·
            refine ⟨6268107423815747366833453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8357476565087663155777937 6268107423815747366833453)
            ·
              refine ⟨2350540283930905262562545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6268107423815747366833453 2350540283930905262562545)
              ·
                refine ⟨1762905212948178946921909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350540283930905262562545 1762905212948178946921909)
                ·
                  refine ⟨165272363713891776273929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1762905212948178946921909 165272363713891776273929)
                  ·
                    rfl

theorem cell23_2896801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 5].length) (baseStart_2896801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896801 prefixEnd_2896801 := by exact prefixLift 2896801
  have htrace : WordTrace (prefixWord ++ tailWord_2896801) baseStart_2896801 baseEnd_2896801 := by
    simpa [prefixWord, tailWord_2896801, baseEnd_2896801] using wordTrace_append hprefix tailTrace_2896801
  have hstable : (prefixWord ++ tailWord_2896801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896801).length < 2 ^ (prefixWord ++ tailWord_2896801).sum := by decide
  have hdescent : baseEnd_2896801 < baseStart_2896801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896857 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 6]
def baseStart_2896857 : Nat := 118140960795 + 2896857 * 2 ^ 59
def prefixEnd_2896857 : Nat := 4983230072969 + 3 ^ 40 * 2896857 * 2
def baseEnd_2896857 : Nat := 165275558704630863040567

theorem tailTrace_2896857 : CollatzResearch.WordTrace tailWord_2896857 prefixEnd_2896857 165275558704630863040567 := by
  unfold tailWord_2896857
  simp only [CollatzResearch.WordTrace]
  refine ⟨105657054866189307632144825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70438036577459538421429883 105657054866189307632144825)
  ·
    refine ⟨79242791149641980724108619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105657054866189307632144825 79242791149641980724108619)
    ·
      refine ⟨118864186724462971086162929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79242791149641980724108619 118864186724462971086162929)
      ·
        refine ⟨89148140043347228314622197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118864186724462971086162929 89148140043347228314622197)
        ·
          refine ⟨8357638129063802654495831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89148140043347228314622197 8357638129063802654495831)
          ·
            refine ⟨12536457193595703981743747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357638129063802654495831 12536457193595703981743747)
            ·
              refine ⟨18804685790393555972615621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12536457193595703981743747 18804685790393555972615621)
              ·
                refine ⟨3525878585698791744865429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18804685790393555972615621 3525878585698791744865429)
                ·
                  refine ⟨165275558704630863040567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3525878585698791744865429 165275558704630863040567)
                  ·
                    rfl

theorem cell23_2896857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_2896857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896857 prefixEnd_2896857 := by exact prefixLift 2896857
  have htrace : WordTrace (prefixWord ++ tailWord_2896857) baseStart_2896857 baseEnd_2896857 := by
    simpa [prefixWord, tailWord_2896857, baseEnd_2896857] using wordTrace_append hprefix tailTrace_2896857
  have hstable : (prefixWord ++ tailWord_2896857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896857).length < 2 ^ (prefixWord ++ tailWord_2896857).sum := by decide
  have hdescent : baseEnd_2896857 < baseStart_2896857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896880 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_2896880 : Nat := 118140960795 + 2896880 * 2 ^ 59
def prefixEnd_2896880 : Nat := 4983230072969 + 3 ^ 40 * 2896880 * 2
def baseEnd_2896880 : Nat := 1487491838396731177377497

theorem tailTrace_2896880 : CollatzResearch.WordTrace tailWord_2896880 prefixEnd_2896880 1487491838396731177377497 := by
  unfold tailWord_2896880
  simp only [CollatzResearch.WordTrace]
  refine ⟨52828946872552991280116047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70438595830070655040154729 52828946872552991280116047)
  ·
    refine ⟨79243420308829486920174071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52828946872552991280116047 79243420308829486920174071)
    ·
      refine ⟨118865130463244230380261107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79243420308829486920174071 118865130463244230380261107)
      ·
        refine ⟨178297695694866345570391661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118865130463244230380261107 178297695694866345570391661)
        ·
          refine ⟨66861635885574879588896873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178297695694866345570391661 66861635885574879588896873)
          ·
            refine ⟨50146226914181159691672655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66861635885574879588896873 50146226914181159691672655)
            ·
              refine ⟨75219340371271739537508983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50146226914181159691672655 75219340371271739537508983)
              ·
                refine ⟨112829010556907609306263475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75219340371271739537508983 112829010556907609306263475)
                ·
                  refine ⟨169243515835361413959395213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112829010556907609306263475 169243515835361413959395213)
                  ·
                    refine ⟨63466318438260530234773205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169243515835361413959395213 63466318438260530234773205)
                    ·
                      refine ⟨1487491838396731177377497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63466318438260530234773205 1487491838396731177377497)
                      ·
                        rfl

theorem cell23_2896880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_2896880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896880 prefixEnd_2896880 := by exact prefixLift 2896880
  have htrace : WordTrace (prefixWord ++ tailWord_2896880) baseStart_2896880 baseEnd_2896880 := by
    simpa [prefixWord, tailWord_2896880, baseEnd_2896880] using wordTrace_append hprefix tailTrace_2896880
  have hstable : (prefixWord ++ tailWord_2896880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896880).length < 2 ^ (prefixWord ++ tailWord_2896880).sum := by decide
  have hdescent : baseEnd_2896880 < baseStart_2896880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896885 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2896885 : Nat := 118140960795 + 2896885 * 2 ^ 59
def prefixEnd_2896885 : Nat := 4983230072969 + 3 ^ 40 * 2896885 * 2
def baseEnd_2896885 : Nat := 1487494405800003657814975

theorem tailTrace_2896885 : CollatzResearch.WordTrace tailWord_2896885 prefixEnd_2896885 1487494405800003657814975 := by
  unfold tailWord_2896885
  simp only [CollatzResearch.WordTrace]
  refine ⟨105658076110087868414164109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70438717406725245609442739 105658076110087868414164109)
  ·
    refine ⟨39621778541282950655311541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105658076110087868414164109 39621778541282950655311541)
    ·
      refine ⟨3714541738245276623935457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39621778541282950655311541 3714541738245276623935457)
      ·
        refine ⟨2785906303683957467951593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714541738245276623935457 2785906303683957467951593)
        ·
          refine ⟨2089429727762968100963695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2785906303683957467951593 2089429727762968100963695)
          ·
            refine ⟨3134144591644452151445543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089429727762968100963695 3134144591644452151445543)
            ·
              refine ⟨4701216887466678227168315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134144591644452151445543 4701216887466678227168315)
              ·
                refine ⟨7051825331200017340752473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701216887466678227168315 7051825331200017340752473)
                ·
                  refine ⟨5288868998400013005564355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7051825331200017340752473 5288868998400013005564355)
                  ·
                    refine ⟨7933303497600019508346533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5288868998400013005564355 7933303497600019508346533)
                    ·
                      refine ⟨1487494405800003657814975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7933303497600019508346533 1487494405800003657814975)
                      ·
                        rfl

theorem cell23_2896885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2896885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896885 prefixEnd_2896885 := by exact prefixLift 2896885
  have htrace : WordTrace (prefixWord ++ tailWord_2896885) baseStart_2896885 baseEnd_2896885 := by
    simpa [prefixWord, tailWord_2896885, baseEnd_2896885] using wordTrace_append hprefix tailTrace_2896885
  have hstable : (prefixWord ++ tailWord_2896885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896885).length < 2 ^ (prefixWord ++ tailWord_2896885).sum := by decide
  have hdescent : baseEnd_2896885 < baseStart_2896885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896904 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 1, 5]
def baseStart_2896904 : Nat := 118140960795 + 2896904 * 2 ^ 59
def prefixEnd_2896904 : Nat := 4983230072969 + 3 ^ 40 * 2896904 * 2
def baseEnd_2896904 : Nat := 495834720644146361159129

theorem tailTrace_2896904 : CollatzResearch.WordTrace tailWord_2896904 prefixEnd_2896904 495834720644146361159129 := by
  unfold tailWord_2896904
  simp only [CollatzResearch.WordTrace]
  refine ⟨52829384548509517329552883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70439179398012689772737177 52829384548509517329552883)
  ·
    refine ⟨79244076822764275994329325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52829384548509517329552883 79244076822764275994329325)
    ·
      refine ⟨29716528808536603497873497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79244076822764275994329325 29716528808536603497873497)
      ·
        refine ⟨22287396606402452623405123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29716528808536603497873497 22287396606402452623405123)
        ·
          refine ⟨33431094909603678935107685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22287396606402452623405123 33431094909603678935107685)
          ·
            refine ⟨6268330295550689800332691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33431094909603678935107685 6268330295550689800332691)
            ·
              refine ⟨9402495443326034700499037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268330295550689800332691 9402495443326034700499037)
              ·
                refine ⟨3525935791247263012687139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9402495443326034700499037 3525935791247263012687139)
                ·
                  refine ⟨5288903686870894519030709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3525935791247263012687139 5288903686870894519030709)
                  ·
                    refine ⟨495834720644146361159129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5288903686870894519030709 495834720644146361159129)
                    ·
                      rfl

theorem cell23_2896904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_2896904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896904 prefixEnd_2896904 := by exact prefixLift 2896904
  have htrace : WordTrace (prefixWord ++ tailWord_2896904) baseStart_2896904 baseEnd_2896904 := by
    simpa [prefixWord, tailWord_2896904, baseEnd_2896904] using wordTrace_append hprefix tailTrace_2896904
  have hstable : (prefixWord ++ tailWord_2896904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896904).length < 2 ^ (prefixWord ++ tailWord_2896904).sum := by decide
  have hdescent : baseEnd_2896904 < baseStart_2896904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896927 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2896927 : Nat := 118140960795 + 2896927 * 2 ^ 59
def prefixEnd_2896927 : Nat := 4983230072969 + 3 ^ 40 * 2896927 * 2
def baseEnd_2896927 : Nat := 1487515971987492493489781

theorem tailTrace_2896927 : CollatzResearch.WordTrace tailWord_2896927 prefixEnd_2896927 1487515971987492493489781 := by
  unfold tailWord_2896927
  simp only [CollatzResearch.WordTrace]
  refine ⟨105659607975935709587193035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70439738650623806391462023 105659607975935709587193035)
  ·
    refine ⟨158489411963903564380789553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105659607975935709587193035 158489411963903564380789553)
    ·
      refine ⟨118867058972927673285592165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158489411963903564380789553 118867058972927673285592165)
      ·
        refine ⟨22287573557423938741048531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118867058972927673285592165 22287573557423938741048531)
        ·
          refine ⟨33431360336135908111572797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22287573557423938741048531 33431360336135908111572797)
          ·
            refine ⟨12536760126050965541839799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33431360336135908111572797 12536760126050965541839799)
            ·
              refine ⟨18805140189076448312759699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12536760126050965541839799 18805140189076448312759699)
              ·
                refine ⟨28207710283614672469139549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18805140189076448312759699 28207710283614672469139549)
                ·
                  refine ⟨10577891356355502175927331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28207710283614672469139549 10577891356355502175927331)
                  ·
                    refine ⟨15866837034533253263890997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10577891356355502175927331 15866837034533253263890997)
                    ·
                      refine ⟨1487515971987492493489781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15866837034533253263890997 1487515971987492493489781)
                      ·
                        rfl

theorem cell23_2896927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2896927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896927 prefixEnd_2896927 := by exact prefixLift 2896927
  have htrace : WordTrace (prefixWord ++ tailWord_2896927) baseStart_2896927 baseEnd_2896927 := by
    simpa [prefixWord, tailWord_2896927, baseEnd_2896927] using wordTrace_append hprefix tailTrace_2896927
  have hstable : (prefixWord ++ tailWord_2896927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896927).length < 2 ^ (prefixWord ++ tailWord_2896927).sum := by decide
  have hdescent : baseEnd_2896927 < baseStart_2896927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896961 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2896961 : Nat := 118140960795 + 2896961 * 2 ^ 59
def prefixEnd_2896961 : Nat := 4983230072969 + 3 ^ 40 * 2896961 * 2
def baseEnd_2896961 : Nat := 1487533430329745360464625

theorem tailTrace_2896961 : CollatzResearch.WordTrace tailWord_2896961 prefixEnd_2896961 1487533430329745360464625 := by
  unfold tailWord_2896961
  simp only [CollatzResearch.WordTrace]
  refine ⟨105660848057812533393930737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70440565371875022262620491 105660848057812533393930737)
  ·
    refine ⟨79245636043359400045448053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105660848057812533393930737 79245636043359400045448053)
    ·
      refine ⟨7429278379064943754260755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79245636043359400045448053 7429278379064943754260755)
      ·
        refine ⟨11143917568597415631391133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7429278379064943754260755 11143917568597415631391133)
        ·
          refine ⟨4178969088224030861771675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11143917568597415631391133 4178969088224030861771675)
          ·
            refine ⟨6268453632336046292657513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178969088224030861771675 6268453632336046292657513)
            ·
              refine ⟨4701340224252034719493135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6268453632336046292657513 4701340224252034719493135)
              ·
                refine ⟨7052010336378052079239703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701340224252034719493135 7052010336378052079239703)
                ·
                  refine ⟨10578015504567078118859555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052010336378052079239703 10578015504567078118859555)
                  ·
                    refine ⟨15867023256850617178289333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10578015504567078118859555 15867023256850617178289333)
                    ·
                      refine ⟨1487533430329745360464625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15867023256850617178289333 1487533430329745360464625)
                      ·
                        rfl

theorem cell23_2896961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2896961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896961 prefixEnd_2896961 := by exact prefixLift 2896961
  have htrace : WordTrace (prefixWord ++ tailWord_2896961) baseStart_2896961 baseEnd_2896961 := by
    simpa [prefixWord, tailWord_2896961, baseEnd_2896961] using wordTrace_append hprefix tailTrace_2896961
  have hstable : (prefixWord ++ tailWord_2896961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896961).length < 2 ^ (prefixWord ++ tailWord_2896961).sum := by decide
  have hdescent : baseEnd_2896961 < baseStart_2896961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2896991 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 3]
def baseStart_2896991 : Nat := 118140960795 + 2896991 * 2 ^ 59
def prefixEnd_2896991 : Nat := 4983230072969 + 3 ^ 40 * 2896991 * 2
def baseEnd_2896991 : Nat := 1487548834749380243089487

theorem tailTrace_2896991 : CollatzResearch.WordTrace tailWord_2896991 prefixEnd_2896991 1487548834749380243089487 := by
  unfold tailWord_2896991
  simp only [CollatzResearch.WordTrace]
  refine ⟨105661942247703848517522827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70441294831802565678348551 105661942247703848517522827)
  ·
    refine ⟨158492913371555772776284241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105661942247703848517522827 158492913371555772776284241)
    ·
      refine ⟨118869685028666829582213181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158492913371555772776284241 118869685028666829582213181)
      ·
        refine ⟨44576131885750061093329943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118869685028666829582213181 44576131885750061093329943)
        ·
          refine ⟨66864197828625091639994915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44576131885750061093329943 66864197828625091639994915)
          ·
            refine ⟨100296296742937637459992373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66864197828625091639994915 100296296742937637459992373)
            ·
              refine ⟨9402777819650403511874285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100296296742937637459992373 9402777819650403511874285)
              ·
                refine ⟨3526041682368901316952857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9402777819650403511874285 3526041682368901316952857)
                ·
                  refine ⟨2644531261776675987714643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3526041682368901316952857 2644531261776675987714643)
                  ·
                    refine ⟨3966796892665013981571965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2644531261776675987714643 3966796892665013981571965)
                    ·
                      refine ⟨1487548834749380243089487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3966796892665013981571965 1487548834749380243089487)
                      ·
                        rfl

theorem cell23_2896991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_2896991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2896991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2896991 prefixEnd_2896991 := by exact prefixLift 2896991
  have htrace : WordTrace (prefixWord ++ tailWord_2896991) baseStart_2896991 baseEnd_2896991 := by
    simpa [prefixWord, tailWord_2896991, baseEnd_2896991] using wordTrace_append hprefix tailTrace_2896991
  have hstable : (prefixWord ++ tailWord_2896991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2896991).length < 2 ^ (prefixWord ++ tailWord_2896991).sum := by decide
  have hdescent : baseEnd_2896991 < baseStart_2896991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2896991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897001 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 3, 3, 2]
def baseStart_2897001 : Nat := 118140960795 + 2897001 * 2 ^ 59
def prefixEnd_2897001 : Nat := 4983230072969 + 3 ^ 40 * 2897001 * 2
def baseEnd_2897001 : Nat := 1487553969555925203964441

theorem tailTrace_2897001 : CollatzResearch.WordTrace tailWord_2897001 prefixEnd_2897001 1487553969555925203964441 := by
  unfold tailWord_2897001
  simp only [CollatzResearch.WordTrace]
  refine ⟨105662306977667620225386857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70441537985111746816924571 105662306977667620225386857)
  ·
    refine ⟨79246730233250715169040143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105662306977667620225386857 79246730233250715169040143)
    ·
      refine ⟨118870095349876072753560215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79246730233250715169040143 118870095349876072753560215)
      ·
        refine ⟨178305143024814109130340323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118870095349876072753560215 178305143024814109130340323)
        ·
          refine ⟨267457714537221163695510485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178305143024814109130340323 267457714537221163695510485)
          ·
            refine ⟨6268540184466121024113527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 267457714537221163695510485 6268540184466121024113527)
            ·
              refine ⟨9402810276699181536170291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268540184466121024113527 9402810276699181536170291)
              ·
                refine ⟨14104215415048772304255437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9402810276699181536170291 14104215415048772304255437)
                ·
                  refine ⟨5289080780643289614095789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14104215415048772304255437 5289080780643289614095789)
                  ·
                    refine ⟨1983405292741233605285921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5289080780643289614095789 1983405292741233605285921)
                    ·
                      refine ⟨1487553969555925203964441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1983405292741233605285921 1487553969555925203964441)
                      ·
                        rfl

theorem cell23_2897001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 3, 2].length) (baseStart_2897001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897001 prefixEnd_2897001 := by exact prefixLift 2897001
  have htrace : WordTrace (prefixWord ++ tailWord_2897001) baseStart_2897001 baseEnd_2897001 := by
    simpa [prefixWord, tailWord_2897001, baseEnd_2897001] using wordTrace_append hprefix tailTrace_2897001
  have hstable : (prefixWord ++ tailWord_2897001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897001).length < 2 ^ (prefixWord ++ tailWord_2897001).sum := by decide
  have hdescent : baseEnd_2897001 < baseStart_2897001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897034 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2897034 : Nat := 118140960795 + 2897034 * 2 ^ 59
def prefixEnd_2897034 : Nat := 4983230072969 + 3 ^ 40 * 2897034 * 2
def baseEnd_2897034 : Nat := 1487570914417523574851789

theorem tailTrace_2897034 : CollatzResearch.WordTrace tailWord_2897034 prefixEnd_2897034 1487570914417523574851789 := by
  unfold tailWord_2897034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26415877646637016715334539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70442340391032044574225437 26415877646637016715334539)
  ·
    refine ⟨39623816469955525073001809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26415877646637016715334539 39623816469955525073001809)
    ·
      refine ⟨29717862352466643804751357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39623816469955525073001809 29717862352466643804751357)
      ·
        refine ⟨11144198382174991426781759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29717862352466643804751357 11144198382174991426781759)
        ·
          refine ⟨16716297573262487140172639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11144198382174991426781759 16716297573262487140172639)
          ·
            refine ⟨25074446359893730710258959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16716297573262487140172639 25074446359893730710258959)
            ·
              refine ⟨37611669539840596065388439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25074446359893730710258959 37611669539840596065388439)
              ·
                refine ⟨56417504309760894098082659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37611669539840596065388439 56417504309760894098082659)
                ·
                  refine ⟨84626256464641341147123989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56417504309760894098082659 84626256464641341147123989)
                  ·
                    refine ⟨3966855771780062866271437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84626256464641341147123989 3966855771780062866271437)
                    ·
                      refine ⟨1487570914417523574851789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3966855771780062866271437 1487570914417523574851789)
                      ·
                        rfl

theorem cell23_2897034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2897034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897034 prefixEnd_2897034 := by exact prefixLift 2897034
  have htrace : WordTrace (prefixWord ++ tailWord_2897034) baseStart_2897034 baseEnd_2897034 := by
    simpa [prefixWord, tailWord_2897034, baseEnd_2897034] using wordTrace_append hprefix tailTrace_2897034
  have hstable : (prefixWord ++ tailWord_2897034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897034).length < 2 ^ (prefixWord ++ tailWord_2897034).sum := by decide
  have hdescent : baseEnd_2897034 < baseStart_2897034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897048 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 1, 4, 2]
def baseStart_2897048 : Nat := 118140960795 + 2897048 * 2 ^ 59
def prefixEnd_2897048 : Nat := 4983230072969 + 3 ^ 40 * 2897048 * 2
def baseEnd_2897048 : Nat := 1487578103146686520076725

theorem tailTrace_2897048 : CollatzResearch.WordTrace tailWord_2897048 prefixEnd_2897048 1487578103146686520076725 := by
  unfold tailWord_2897048
  simp only [CollatzResearch.WordTrace]
  refine ⟨52832010604248673626173899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70442680805664898168231865 52832010604248673626173899)
  ·
    refine ⟨79248015906373010439260849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52832010604248673626173899 79248015906373010439260849)
    ·
      refine ⟨59436011929779757829445637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79248015906373010439260849 59436011929779757829445637)
      ·
        refine ⟨11144252236833704593021057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59436011929779757829445637 11144252236833704593021057)
        ·
          refine ⟨8358189177625278444765793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11144252236833704593021057 8358189177625278444765793)
          ·
            refine ⟨6268641883218958833574345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8358189177625278444765793 6268641883218958833574345)
            ·
              refine ⟨4701481412414219125180759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6268641883218958833574345 4701481412414219125180759)
              ·
                refine ⟨7052222118621328687771139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701481412414219125180759 7052222118621328687771139)
                ·
                  refine ⟨10578333177931993031656709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052222118621328687771139 10578333177931993031656709)
                  ·
                    refine ⟨1983437470862248693435633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10578333177931993031656709 1983437470862248693435633)
                    ·
                      refine ⟨1487578103146686520076725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1983437470862248693435633 1487578103146686520076725)
                      ·
                        rfl

theorem cell23_2897048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_2897048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897048 prefixEnd_2897048 := by exact prefixLift 2897048
  have htrace : WordTrace (prefixWord ++ tailWord_2897048) baseStart_2897048 baseEnd_2897048 := by
    simpa [prefixWord, tailWord_2897048, baseEnd_2897048] using wordTrace_append hprefix tailTrace_2897048
  have hstable : (prefixWord ++ tailWord_2897048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897048).length < 2 ^ (prefixWord ++ tailWord_2897048).sum := by decide
  have hdescent : baseEnd_2897048 < baseStart_2897048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897069 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_2897069 : Nat := 118140960795 + 2897069 * 2 ^ 59
def prefixEnd_2897069 : Nat := 4983230072969 + 3 ^ 40 * 2897069 * 2
def baseEnd_2897069 : Nat := 1487588886240430937914129

theorem tailTrace_2897069 : CollatzResearch.WordTrace tailWord_2897069 prefixEnd_2897069 1487588886240430937914129 := by
  unfold tailWord_2897069
  simp only [CollatzResearch.WordTrace]
  refine ⟨105664787141421267838862261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70443191427614178559241507 105664787141421267838862261)
  ·
    refine ⟨9906073794508243859893337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105664787141421267838862261 9906073794508243859893337)
    ·
      refine ⟨7429555345881182894920003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9906073794508243859893337 7429555345881182894920003)
      ·
        refine ⟨11144333018821774342380005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7429555345881182894920003 11144333018821774342380005)
        ·
          refine ⟨2089562441029082689196251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11144333018821774342380005 2089562441029082689196251)
          ·
            refine ⟨3134343661543624033794377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089562441029082689196251 3134343661543624033794377)
            ·
              refine ⟨2350757746157718025345783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134343661543624033794377 2350757746157718025345783)
              ·
                refine ⟨3526136619236577038018675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350757746157718025345783 3526136619236577038018675)
                ·
                  refine ⟨5289204928854865557028013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526136619236577038018675 5289204928854865557028013)
                  ·
                    refine ⟨1983451848320574583885505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5289204928854865557028013 1983451848320574583885505)
                    ·
                      refine ⟨1487588886240430937914129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1983451848320574583885505 1487588886240430937914129)
                      ·
                        rfl

theorem cell23_2897069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_2897069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897069 prefixEnd_2897069 := by exact prefixLift 2897069
  have htrace : WordTrace (prefixWord ++ tailWord_2897069) baseStart_2897069 baseEnd_2897069 := by
    simpa [prefixWord, tailWord_2897069, baseEnd_2897069] using wordTrace_append hprefix tailTrace_2897069
  have hstable : (prefixWord ++ tailWord_2897069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897069).length < 2 ^ (prefixWord ++ tailWord_2897069).sum := by decide
  have hdescent : baseEnd_2897069 < baseStart_2897069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897134 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2897134 : Nat := 118140960795 + 2897134 * 2 ^ 59
def prefixEnd_2897134 : Nat := 4983230072969 + 3 ^ 40 * 2897134 * 2
def baseEnd_2897134 : Nat := 1487622262482973183601329

theorem tailTrace_2897134 : CollatzResearch.WordTrace tailWord_2897134 prefixEnd_2897134 1487622262482973183601329 := by
  unfold tailWord_2897134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208394735773222992497307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70444771924123855959985637 13208394735773222992497307)
  ·
    refine ⟨19812592103659834488745961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13208394735773222992497307 19812592103659834488745961)
    ·
      refine ⟨14859444077744875866559471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19812592103659834488745961 14859444077744875866559471)
      ·
        refine ⟨22289166116617313799839207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14859444077744875866559471 22289166116617313799839207)
        ·
          refine ⟨33433749174925970699758811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22289166116617313799839207 33433749174925970699758811)
          ·
            refine ⟨50150623762388956049638217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33433749174925970699758811 50150623762388956049638217)
            ·
              refine ⟨37612967821791717037228663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50150623762388956049638217 37612967821791717037228663)
              ·
                refine ⟨56419451732687575555842995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37612967821791717037228663 56419451732687575555842995)
                ·
                  refine ⟨84629177599031363333764493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56419451732687575555842995 84629177599031363333764493)
                  ·
                    refine ⟨31735941599636761250161685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84629177599031363333764493 31735941599636761250161685)
                    ·
                      refine ⟨1487622262482973183601329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31735941599636761250161685 1487622262482973183601329)
                      ·
                        rfl

theorem cell23_2897134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2897134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897134 prefixEnd_2897134 := by exact prefixLift 2897134
  have htrace : WordTrace (prefixWord ++ tailWord_2897134) baseStart_2897134 baseEnd_2897134 := by
    simpa [prefixWord, tailWord_2897134, baseEnd_2897134] using wordTrace_append hprefix tailTrace_2897134
  have hstable : (prefixWord ++ tailWord_2897134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897134).length < 2 ^ (prefixWord ++ tailWord_2897134).sum := by decide
  have hdescent : baseEnd_2897134 < baseStart_2897134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897138 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2897138 : Nat := 118140960795 + 2897138 * 2 ^ 59
def prefixEnd_2897138 : Nat := 4983230072969 + 3 ^ 40 * 2897138 * 2
def baseEnd_2897138 : Nat := 1487624316405591167951311

theorem tailTrace_2897138 : CollatzResearch.WordTrace tailWord_2897138 prefixEnd_2897138 1487624316405591167951311 := by
  unfold tailWord_2897138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26416825944542823155781017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70444869185447528415416045 26416825944542823155781017)
  ·
    refine ⟨19812619458407117366835763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26416825944542823155781017 19812619458407117366835763)
    ·
      refine ⟨29718929187610676050253645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19812619458407117366835763 29718929187610676050253645)
      ·
        refine ⟨11144598445354003518845117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29718929187610676050253645 11144598445354003518845117)
        ·
          refine ⟨4179224417007751319566919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11144598445354003518845117 4179224417007751319566919)
          ·
            refine ⟨6268836625511626979350379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179224417007751319566919 6268836625511626979350379)
            ·
              refine ⟨9403254938267440469025569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6268836625511626979350379 9403254938267440469025569)
              ·
                refine ⟨7052441203700580351769177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9403254938267440469025569 7052441203700580351769177)
                ·
                  refine ⟨5289330902775435263826883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7052441203700580351769177 5289330902775435263826883)
                  ·
                    refine ⟨7933996354163152895740325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5289330902775435263826883 7933996354163152895740325)
                    ·
                      refine ⟨1487624316405591167951311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7933996354163152895740325 1487624316405591167951311)
                      ·
                        rfl

theorem cell23_2897138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2897138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897138 prefixEnd_2897138 := by exact prefixLift 2897138
  have htrace : WordTrace (prefixWord ++ tailWord_2897138) baseStart_2897138 baseEnd_2897138 := by
    simpa [prefixWord, tailWord_2897138, baseEnd_2897138] using wordTrace_append hprefix tailTrace_2897138
  have hstable : (prefixWord ++ tailWord_2897138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897138).length < 2 ^ (prefixWord ++ tailWord_2897138).sum := by decide
  have hdescent : baseEnd_2897138 < baseStart_2897138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897241 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2897241 : Nat := 118140960795 + 2897241 * 2 ^ 59
def prefixEnd_2897241 : Nat := 4983230072969 + 3 ^ 40 * 2897241 * 2
def baseEnd_2897241 : Nat := 1487677204913004264963337

theorem tailTrace_2897241 : CollatzResearch.WordTrace tailWord_2897241 prefixEnd_2897241 1487677204913004264963337 := by
  unfold tailWord_2897241
  simp only [CollatzResearch.WordTrace]
  refine ⟨105671060496798141214123577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70447373664532094142749051 105671060496798141214123577)
  ·
    refine ⟨79253295372598605910592683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105671060496798141214123577 79253295372598605910592683)
    ·
      refine ⟨118879943058897908865889025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79253295372598605910592683 118879943058897908865889025)
      ·
        refine ⟨89159957294173431649416769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118879943058897908865889025 89159957294173431649416769)
        ·
          refine ⟨66869967970630073737062577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89159957294173431649416769 66869967970630073737062577)
          ·
            refine ⟨50152475977972555302796933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66869967970630073737062577 50152475977972555302796933)
            ·
              refine ⟨9403589245869854119274425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50152475977972555302796933 9403589245869854119274425)
              ·
                refine ⟨7052691934402390589455819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9403589245869854119274425 7052691934402390589455819)
                ·
                  refine ⟨10579037901603585884183729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052691934402390589455819 10579037901603585884183729)
                  ·
                    refine ⟨7934278426202689413137797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10579037901603585884183729 7934278426202689413137797)
                    ·
                      refine ⟨1487677204913004264963337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7934278426202689413137797 1487677204913004264963337)
                      ·
                        rfl

theorem cell23_2897241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2897241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897241 prefixEnd_2897241 := by exact prefixLift 2897241
  have htrace : WordTrace (prefixWord ++ tailWord_2897241) baseStart_2897241 baseEnd_2897241 := by
    simpa [prefixWord, tailWord_2897241, baseEnd_2897241] using wordTrace_append hprefix tailTrace_2897241
  have hstable : (prefixWord ++ tailWord_2897241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897241).length < 2 ^ (prefixWord ++ tailWord_2897241).sum := by decide
  have hdescent : baseEnd_2897241 < baseStart_2897241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897282 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2897282 : Nat := 118140960795 + 2897282 * 2 ^ 59
def prefixEnd_2897282 : Nat := 4983230072969 + 3 ^ 40 * 2897282 * 2
def baseEnd_2897282 : Nat := 1487698257619838604550649

theorem tailTrace_2897282 : CollatzResearch.WordTrace tailWord_2897282 prefixEnd_2897282 1487698257619838604550649 := by
  unfold tailWord_2897282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26418138972412401304091525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70448370593099736810910733 26418138972412401304091525)
  ·
    refine ⟨4953401057327325244517161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26418138972412401304091525 4953401057327325244517161)
    ·
      refine ⟨3715050792995493933387871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4953401057327325244517161 3715050792995493933387871)
      ·
        refine ⟨5572576189493240900081807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3715050792995493933387871 5572576189493240900081807)
        ·
          refine ⟨8358864284239861350122711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5572576189493240900081807 8358864284239861350122711)
          ·
            refine ⟨12538296426359792025184067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8358864284239861350122711 12538296426359792025184067)
            ·
              refine ⟨18807444639539688037776101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12538296426359792025184067 18807444639539688037776101)
              ·
                refine ⟨3526395869913691507083019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18807444639539688037776101 3526395869913691507083019)
                ·
                  refine ⟨5289593804870537260624529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526395869913691507083019 5289593804870537260624529)
                  ·
                    refine ⟨3967195353652902945468397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5289593804870537260624529 3967195353652902945468397)
                    ·
                      refine ⟨1487698257619838604550649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3967195353652902945468397 1487698257619838604550649)
                      ·
                        rfl

theorem cell23_2897282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2897282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897282 prefixEnd_2897282 := by exact prefixLift 2897282
  have htrace : WordTrace (prefixWord ++ tailWord_2897282) baseStart_2897282 baseEnd_2897282 := by
    simpa [prefixWord, tailWord_2897282, baseEnd_2897282] using wordTrace_append hprefix tailTrace_2897282
  have hstable : (prefixWord ++ tailWord_2897282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897282).length < 2 ^ (prefixWord ++ tailWord_2897282).sum := by decide
  have hdescent : baseEnd_2897282 < baseStart_2897282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897305 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 1, 3, 2]
def baseStart_2897305 : Nat := 118140960795 + 2897305 * 2 ^ 59
def prefixEnd_2897305 : Nat := 4983230072969 + 3 ^ 40 * 2897305 * 2
def baseEnd_2897305 : Nat := 1487710067674892014563043

theorem tailTrace_2897305 : CollatzResearch.WordTrace tailWord_2897305 prefixEnd_2897305 1487710067674892014563043 := by
  unfold tailWord_2897305
  simp only [CollatzResearch.WordTrace]
  refine ⟨105673394768566280144453369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70448929845710853429635579 105673394768566280144453369)
  ·
    refine ⟨79255046076424710108340027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105673394768566280144453369 79255046076424710108340027)
    ·
      refine ⟨118882569114637065162510041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79255046076424710108340027 118882569114637065162510041)
      ·
        refine ⟨89161926835977798871882531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118882569114637065162510041 89161926835977798871882531)
        ·
          refine ⟨133742890253966698307823797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89161926835977798871882531 133742890253966698307823797)
          ·
            refine ⟨12538395961309377966358481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133742890253966698307823797 12538395961309377966358481)
            ·
              refine ⟨9403796970982033474768861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12538395961309377966358481 9403796970982033474768861)
              ·
                refine ⟨3526423864118262553038323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9403796970982033474768861 3526423864118262553038323)
                ·
                  refine ⟨5289635796177393829557485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526423864118262553038323 5289635796177393829557485)
                  ·
                    refine ⟨1983613423566522686084057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5289635796177393829557485 1983613423566522686084057)
                    ·
                      refine ⟨1487710067674892014563043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1983613423566522686084057 1487710067674892014563043)
                      ·
                        rfl

theorem cell23_2897305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_2897305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897305 prefixEnd_2897305 := by exact prefixLift 2897305
  have htrace : WordTrace (prefixWord ++ tailWord_2897305) baseStart_2897305 baseEnd_2897305 := by
    simpa [prefixWord, tailWord_2897305, baseEnd_2897305] using wordTrace_append hprefix tailTrace_2897305
  have hstable : (prefixWord ++ tailWord_2897305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897305).length < 2 ^ (prefixWord ++ tailWord_2897305).sum := by decide
  have hdescent : baseEnd_2897305 < baseStart_2897305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897331 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4]
def baseStart_2897331 : Nat := 118140960795 + 2897331 * 2 ^ 59
def prefixEnd_2897331 : Nat := 4983230072969 + 3 ^ 40 * 2897331 * 2
def baseEnd_2897331 : Nat := 1487723418171908912837923

theorem tailTrace_2897331 : CollatzResearch.WordTrace tailWord_2897331 prefixEnd_2897331 1487723418171908912837923 := by
  unfold tailWord_2897331
  simp only [CollatzResearch.WordTrace]
  refine ⟨105674343066472086584899847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70449562044314724389933231 105674343066472086584899847)
  ·
    refine ⟨158511514599708129877349771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105674343066472086584899847 158511514599708129877349771)
    ·
      refine ⟨237767271899562194816024657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158511514599708129877349771 237767271899562194816024657)
      ·
        refine ⟨178325453924671646112018493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237767271899562194816024657 178325453924671646112018493)
        ·
          refine ⟨66872045221751867292006935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178325453924671646112018493 66872045221751867292006935)
          ·
            refine ⟨100308067832627800938010403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66872045221751867292006935 100308067832627800938010403)
            ·
              refine ⟨150462101748941701407015605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100308067832627800938010403 150462101748941701407015605)
              ·
                refine ⟨14105822038963284506907713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150462101748941701407015605 14105822038963284506907713)
                ·
                  refine ⟨10579366529222463380180785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14105822038963284506907713 10579366529222463380180785)
                  ·
                    refine ⟨7934524896916847535135589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10579366529222463380180785 7934524896916847535135589)
                    ·
                      refine ⟨1487723418171908912837923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7934524896916847535135589 1487723418171908912837923)
                      ·
                        rfl

theorem cell23_2897331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_2897331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897331 prefixEnd_2897331 := by exact prefixLift 2897331
  have htrace : WordTrace (prefixWord ++ tailWord_2897331) baseStart_2897331 baseEnd_2897331 := by
    simpa [prefixWord, tailWord_2897331, baseEnd_2897331] using wordTrace_append hprefix tailTrace_2897331
  have hstable : (prefixWord ++ tailWord_2897331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897331).length < 2 ^ (prefixWord ++ tailWord_2897331).sum := by decide
  have hdescent : baseEnd_2897331 < baseStart_2897331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897341 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 9]
def baseStart_2897341 : Nat := 118140960795 + 2897341 * 2 ^ 59
def prefixEnd_2897341 : Nat := 4983230072969 + 3 ^ 40 * 2897341 * 2
def baseEnd_2897341 : Nat := 165303172553161541523653

theorem tailTrace_2897341 : CollatzResearch.WordTrace tailWord_2897341 prefixEnd_2897341 165303172553161541523653 := by
  unfold tailWord_2897341
  simp only [CollatzResearch.WordTrace]
  refine ⟨105674707796435858292763877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70449805197623905528509251 105674707796435858292763877)
  ·
    refine ⟨19814007711831723429893227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105674707796435858292763877 19814007711831723429893227)
    ·
      refine ⟨29721011567747585144839841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19814007711831723429893227 29721011567747585144839841)
      ·
        refine ⟨22290758675810688858629881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29721011567747585144839841 22290758675810688858629881)
        ·
          refine ⟨16718069006858016643972411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22290758675810688858629881 16718069006858016643972411)
          ·
            refine ⟨25077103510287024965958617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16718069006858016643972411 25077103510287024965958617)
            ·
              refine ⟨18807827632715268724468963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25077103510287024965958617 18807827632715268724468963)
              ·
                refine ⟨28211741449072903086703445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18807827632715268724468963 28211741449072903086703445)
                ·
                  refine ⟨165303172553161541523653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28211741449072903086703445 165303172553161541523653)
                  ·
                    rfl

theorem cell23_2897341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_2897341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897341 prefixEnd_2897341 := by exact prefixLift 2897341
  have htrace : WordTrace (prefixWord ++ tailWord_2897341) baseStart_2897341 baseEnd_2897341 := by
    simpa [prefixWord, tailWord_2897341, baseEnd_2897341] using wordTrace_append hprefix tailTrace_2897341
  have hstable : (prefixWord ++ tailWord_2897341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897341).length < 2 ^ (prefixWord ++ tailWord_2897341).sum := by decide
  have hdescent : baseEnd_2897341 < baseStart_2897341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897346 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2897346 : Nat := 118140960795 + 2897346 * 2 ^ 59
def prefixEnd_2897346 : Nat := 4983230072969 + 3 ^ 40 * 2897346 * 2
def baseEnd_2897346 : Nat := 1487731120381726354150355

theorem tailTrace_2897346 : CollatzResearch.WordTrace tailWord_2897346 prefixEnd_2897346 1487731120381726354150355 := by
  unfold tailWord_2897346
  simp only [CollatzResearch.WordTrace]
  refine ⟨26418722540354436036673973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70449926774278496097797261 26418722540354436036673973)
  ·
    refine ⟨2476755238158228378438185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26418722540354436036673973 2476755238158228378438185)
    ·
      refine ⟨1857566428618671283828639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2476755238158228378438185 1857566428618671283828639)
      ·
        refine ⟨2786349642928006925742959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857566428618671283828639 2786349642928006925742959)
        ·
          refine ⟨4179524464392010388614439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786349642928006925742959 4179524464392010388614439)
          ·
            refine ⟨6269286696588015582921659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179524464392010388614439 6269286696588015582921659)
            ·
              refine ⟨9403930044882023374382489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6269286696588015582921659 9403930044882023374382489)
              ·
                refine ⟨7052947533661517530786867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9403930044882023374382489 7052947533661517530786867)
                ·
                  refine ⟨10579421300492276296180301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7052947533661517530786867 10579421300492276296180301)
                  ·
                    refine ⟨3967282987684603611067613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10579421300492276296180301 3967282987684603611067613)
                    ·
                      refine ⟨1487731120381726354150355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3967282987684603611067613 1487731120381726354150355)
                      ·
                        rfl

theorem cell23_2897346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2897346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897346 prefixEnd_2897346 := by exact prefixLift 2897346
  have htrace : WordTrace (prefixWord ++ tailWord_2897346) baseStart_2897346 baseEnd_2897346 := by
    simpa [prefixWord, tailWord_2897346, baseEnd_2897346] using wordTrace_append hprefix tailTrace_2897346
  have hstable : (prefixWord ++ tailWord_2897346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897346).length < 2 ^ (prefixWord ++ tailWord_2897346).sum := by decide
  have hdescent : baseEnd_2897346 < baseStart_2897346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897405 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2897405 : Nat := 118140960795 + 2897405 * 2 ^ 59
def prefixEnd_2897405 : Nat := 4983230072969 + 3 ^ 40 * 2897405 * 2
def baseEnd_2897405 : Nat := 495920471913447207770861

theorem tailTrace_2897405 : CollatzResearch.WordTrace tailWord_2897405 prefixEnd_2897405 495920471913447207770861 := by
  unfold tailWord_2897405
  simp only [CollatzResearch.WordTrace]
  refine ⟨105677042068203997223093669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70451361378802664815395779 105677042068203997223093669)
  ·
    refine ⟨19814445387788249479330063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105677042068203997223093669 19814445387788249479330063)
    ·
      refine ⟨29721668081682374218995095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19814445387788249479330063 29721668081682374218995095)
      ·
        refine ⟨44582502122523561328492643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29721668081682374218995095 44582502122523561328492643)
        ·
          refine ⟨66873753183785341992738965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44582502122523561328492643 66873753183785341992738965)
          ·
            refine ⟨3134707180489937905909639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66873753183785341992738965 3134707180489937905909639)
            ·
              refine ⟨4702060770734906858864459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134707180489937905909639 4702060770734906858864459)
              ·
                refine ⟨7053091156102360288296689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702060770734906858864459 7053091156102360288296689)
                ·
                  refine ⟨5289818367076770216222517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7053091156102360288296689 5289818367076770216222517)
                  ·
                    refine ⟨495920471913447207770861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5289818367076770216222517 495920471913447207770861)
                    ·
                      rfl

theorem cell23_2897405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2897405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897405 prefixEnd_2897405 := by exact prefixLift 2897405
  have htrace : WordTrace (prefixWord ++ tailWord_2897405) baseStart_2897405 baseEnd_2897405 := by
    simpa [prefixWord, tailWord_2897405, baseEnd_2897405] using wordTrace_append hprefix tailTrace_2897405
  have hstable : (prefixWord ++ tailWord_2897405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897405).length < 2 ^ (prefixWord ++ tailWord_2897405).sum := by decide
  have hdescent : baseEnd_2897405 < baseStart_2897405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897411 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_2897411 : Nat := 118140960795 + 2897411 * 2 ^ 59
def prefixEnd_2897411 : Nat := 4983230072969 + 3 ^ 40 * 2897411 * 2
def baseEnd_2897411 : Nat := 1487764496624268599837555

theorem tailTrace_2897411 : CollatzResearch.WordTrace tailWord_2897411 prefixEnd_2897411 1487764496624268599837555 := by
  unfold tailWord_2897411
  simp only [CollatzResearch.WordTrace]
  refine ⟨105677260906182260247812087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70451507270788173498541391 105677260906182260247812087)
  ·
    refine ⟨158515891359273390371718131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105677260906182260247812087 158515891359273390371718131)
    ·
      refine ⟨237773837038910085557577197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158515891359273390371718131 237773837038910085557577197)
      ·
        refine ⟨89165188889591282084091449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237773837038910085557577197 89165188889591282084091449)
        ·
          refine ⟨66873891667193461563068587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89165188889591282084091449 66873891667193461563068587)
          ·
            refine ⟨100310837500790192344602881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66873891667193461563068587 100310837500790192344602881)
            ·
              refine ⟨75233128125592644258452161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100310837500790192344602881 75233128125592644258452161)
              ·
                refine ⟨56424846094194483193839121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75233128125592644258452161 56424846094194483193839121)
                ·
                  refine ⟨42318634570645862395379341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56424846094194483193839121 42318634570645862395379341)
                  ·
                    refine ⟨15869487963992198398267253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42318634570645862395379341 15869487963992198398267253)
                    ·
                      refine ⟨1487764496624268599837555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15869487963992198398267253 1487764496624268599837555)
                      ·
                        rfl

theorem cell23_2897411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_2897411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897411 prefixEnd_2897411 := by exact prefixLift 2897411
  have htrace : WordTrace (prefixWord ++ tailWord_2897411) baseStart_2897411 baseEnd_2897411 := by
    simpa [prefixWord, tailWord_2897411, baseEnd_2897411] using wordTrace_append hprefix tailTrace_2897411
  have hstable : (prefixWord ++ tailWord_2897411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897411).length < 2 ^ (prefixWord ++ tailWord_2897411).sum := by decide
  have hdescent : baseEnd_2897411 < baseStart_2897411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897458 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_2897458 : Nat := 118140960795 + 2897458 * 2 ^ 59
def prefixEnd_2897458 : Nat := 4983230072969 + 3 ^ 40 * 2897458 * 2
def baseEnd_2897458 : Nat := 1487788630215029915949839

theorem tailTrace_2897458 : CollatzResearch.WordTrace tailWord_2897458 prefixEnd_2897458 1487788630215029915949839 := by
  unfold tailWord_2897458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419743784252996818693257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70452650091341324849848685 26419743784252996818693257)
  ·
    refine ⟨19814807838189747614019943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26419743784252996818693257 19814807838189747614019943)
    ·
      refine ⟨29722211757284621421029915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19814807838189747614019943 29722211757284621421029915)
      ·
        refine ⟨44583317635926932131544873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29722211757284621421029915 44583317635926932131544873)
        ·
          refine ⟨33437488226945199098658655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44583317635926932131544873 33437488226945199098658655)
          ·
            refine ⟨50156232340417798647987983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33437488226945199098658655 50156232340417798647987983)
            ·
              refine ⟨75234348510626697971981975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50156232340417798647987983 75234348510626697971981975)
              ·
                refine ⟨112851522765940046957972963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75234348510626697971981975 112851522765940046957972963)
                ·
                  refine ⟨169277284148910070436959445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112851522765940046957972963 169277284148910070436959445)
                  ·
                    refine ⟨3967436347240079775866237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 169277284148910070436959445 3967436347240079775866237)
                    ·
                      refine ⟨1487788630215029915949839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3967436347240079775866237 1487788630215029915949839)
                      ·
                        rfl

theorem cell23_2897458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_2897458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897458 prefixEnd_2897458 := by exact prefixLift 2897458
  have htrace : WordTrace (prefixWord ++ tailWord_2897458) baseStart_2897458 baseEnd_2897458 := by
    simpa [prefixWord, tailWord_2897458, baseEnd_2897458] using wordTrace_append hprefix tailTrace_2897458
  have hstable : (prefixWord ++ tailWord_2897458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897458).length < 2 ^ (prefixWord ++ tailWord_2897458).sum := by decide
  have hdescent : baseEnd_2897458 < baseStart_2897458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897512 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2897512 : Nat := 118140960795 + 2897512 * 2 ^ 59
def prefixEnd_2897512 : Nat := 4983230072969 + 3 ^ 40 * 2897512 * 2
def baseEnd_2897512 : Nat := 495938786056790901558197

theorem tailTrace_2897512 : CollatzResearch.WordTrace tailWord_2897512 prefixEnd_2897512 495938786056790901558197 := by
  unfold tailWord_2897512
  simp only [CollatzResearch.WordTrace]
  refine ⟨52840472339408177248619395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70453963119210902998159193 52840472339408177248619395)
  ·
    refine ⟨79260708509112265872929093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52840472339408177248619395 79260708509112265872929093)
    ·
      refine ⟨14861382845458549851174205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79260708509112265872929093 14861382845458549851174205)
      ·
        refine ⟨5573018567046956194190327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14861382845458549851174205 5573018567046956194190327)
        ·
          refine ⟨8359527850570434291285491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573018567046956194190327 8359527850570434291285491)
          ·
            refine ⟨12539291775855651436928237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359527850570434291285491 12539291775855651436928237)
            ·
              refine ⟨4702234415945869288848089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12539291775855651436928237 4702234415945869288848089)
              ·
                refine ⟨3526675811959401966636067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4702234415945869288848089 3526675811959401966636067)
                ·
                  refine ⟨5290013717939102949954101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3526675811959401966636067 5290013717939102949954101)
                  ·
                    refine ⟨495938786056790901558197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5290013717939102949954101 495938786056790901558197)
                    ·
                      rfl

theorem cell23_2897512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2897512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897512 prefixEnd_2897512 := by exact prefixLift 2897512
  have htrace : WordTrace (prefixWord ++ tailWord_2897512) baseStart_2897512 baseEnd_2897512 := by
    simpa [prefixWord, tailWord_2897512, baseEnd_2897512] using wordTrace_append hprefix tailTrace_2897512
  have hstable : (prefixWord ++ tailWord_2897512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897512).length < 2 ^ (prefixWord ++ tailWord_2897512).sum := by decide
  have hdescent : baseEnd_2897512 < baseStart_2897512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897525 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2897525 : Nat := 118140960795 + 2897525 * 2 ^ 59
def prefixEnd_2897525 : Nat := 4983230072969 + 3 ^ 40 * 2897525 * 2
def baseEnd_2897525 : Nat := 495941011139627051270677

theorem tailTrace_2897525 : CollatzResearch.WordTrace tailWord_2897525 prefixEnd_2897525 495941011139627051270677 := by
  unfold tailWord_2897525
  simp only [CollatzResearch.WordTrace]
  refine ⟨105681418827769257717462029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70454279218512838478308019 105681418827769257717462029)
  ·
    refine ⟨39630532060413471644048261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105681418827769257717462029 39630532060413471644048261)
    ·
      refine ⟨7430724761327525933259049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39630532060413471644048261 7430724761327525933259049)
      ·
        refine ⟨5573043570995644449944287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7430724761327525933259049 5573043570995644449944287)
        ·
          refine ⟨8359565356493466674916431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573043570995644449944287 8359565356493466674916431)
          ·
            refine ⟨12539348034740200012374647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359565356493466674916431 12539348034740200012374647)
            ·
              refine ⟨18809022052110300018561971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12539348034740200012374647 18809022052110300018561971)
              ·
                refine ⟨28213533078165450027842957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18809022052110300018561971 28213533078165450027842957)
                ·
                  refine ⟨10580074904312043760441109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28213533078165450027842957 10580074904312043760441109)
                  ·
                    refine ⟨495941011139627051270677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10580074904312043760441109 495941011139627051270677)
                    ·
                      rfl

theorem cell23_2897525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2897525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897525 prefixEnd_2897525 := by exact prefixLift 2897525
  have htrace : WordTrace (prefixWord ++ tailWord_2897525) baseStart_2897525 baseEnd_2897525 := by
    simpa [prefixWord, tailWord_2897525, baseEnd_2897525] using wordTrace_append hprefix tailTrace_2897525
  have hstable : (prefixWord ++ tailWord_2897525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897525).length < 2 ^ (prefixWord ++ tailWord_2897525).sum := by decide
  have hdescent : baseEnd_2897525 < baseStart_2897525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897566 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2897566 : Nat := 118140960795 + 2897566 * 2 ^ 59
def prefixEnd_2897566 : Nat := 4983230072969 + 3 ^ 40 * 2897566 * 2
def baseEnd_2897566 : Nat := 1487844086125715493399343

theorem tailTrace_2897566 : CollatzResearch.WordTrace tailWord_2897566 prefixEnd_2897566 1487844086125715493399343 := by
  unfold tailWord_2897566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210364277577590214963069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70455276147080481146469701 13210364277577590214963069)
  ·
    refine ⟨4953886604091596330611151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13210364277577590214963069 4953886604091596330611151)
    ·
      refine ⟨7430829906137394495916727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953886604091596330611151 7430829906137394495916727)
      ·
        refine ⟨11146244859206091743875091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430829906137394495916727 11146244859206091743875091)
        ·
          refine ⟨16719367288809137615812637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11146244859206091743875091 16719367288809137615812637)
          ·
            refine ⟨6269762733303426605929739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16719367288809137615812637 6269762733303426605929739)
            ·
              refine ⟨9404644099955139908894609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6269762733303426605929739 9404644099955139908894609)
              ·
                refine ⟨7053483074966354931670957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9404644099955139908894609 7053483074966354931670957)
                ·
                  refine ⟨2645056153112383099376609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7053483074966354931670957 2645056153112383099376609)
                  ·
                    refine ⟨1983792114834287324532457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2645056153112383099376609 1983792114834287324532457)
                    ·
                      refine ⟨1487844086125715493399343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1983792114834287324532457 1487844086125715493399343)
                      ·
                        rfl

theorem cell23_2897566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2897566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897566 prefixEnd_2897566 := by exact prefixLift 2897566
  have htrace : WordTrace (prefixWord ++ tailWord_2897566) baseStart_2897566 baseEnd_2897566 := by
    simpa [prefixWord, tailWord_2897566, baseEnd_2897566] using wordTrace_append hprefix tailTrace_2897566
  have hstable : (prefixWord ++ tailWord_2897566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897566).length < 2 ^ (prefixWord ++ tailWord_2897566).sum := by decide
  have hdescent : baseEnd_2897566 < baseStart_2897566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897655 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_2897655 : Nat := 118140960795 + 2897655 * 2 ^ 59
def prefixEnd_2897655 : Nat := 4983230072969 + 3 ^ 40 * 2897655 * 2
def baseEnd_2897655 : Nat := 1487889785903965645186433

theorem tailTrace_2897655 : CollatzResearch.WordTrace tailWord_2897655 prefixEnd_2897655 1487889785903965645186433 := by
  unfold tailWord_2897655
  simp only [CollatzResearch.WordTrace]
  refine ⟨105686160317298289919694419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70457440211532193279796279 105686160317298289919694419)
  ·
    refine ⟨158529240475947434879541629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105686160317298289919694419 158529240475947434879541629)
    ·
      refine ⟨59448465178480288079828111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158529240475947434879541629 59448465178480288079828111)
      ·
        refine ⟨89172697767720432119742167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59448465178480288079828111 89172697767720432119742167)
        ·
          refine ⟨133759046651580648179613251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89172697767720432119742167 133759046651580648179613251)
          ·
            refine ⟨200638569977370972269419877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133759046651580648179613251 200638569977370972269419877)
            ·
              refine ⟨37619731870757057300516227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200638569977370972269419877 37619731870757057300516227)
              ·
                refine ⟨56429597806135585950774341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37619731870757057300516227 56429597806135585950774341)
                ·
                  refine ⟨10580549588650422365770189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56429597806135585950774341 10580549588650422365770189)
                  ·
                    refine ⟨3967706095743908387163821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10580549588650422365770189 3967706095743908387163821)
                    ·
                      refine ⟨1487889785903965645186433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3967706095743908387163821 1487889785903965645186433)
                      ·
                        rfl

theorem cell23_2897655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_2897655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897655 prefixEnd_2897655 := by exact prefixLift 2897655
  have htrace : WordTrace (prefixWord ++ tailWord_2897655) baseStart_2897655 baseEnd_2897655 := by
    simpa [prefixWord, tailWord_2897655, baseEnd_2897655] using wordTrace_append hprefix tailTrace_2897655
  have hstable : (prefixWord ++ tailWord_2897655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897655).length < 2 ^ (prefixWord ++ tailWord_2897655).sum := by decide
  have hdescent : baseEnd_2897655 < baseStart_2897655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897692 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2897692 : Nat := 118140960795 + 2897692 * 2 ^ 59
def prefixEnd_2897692 : Nat := 4983230072969 + 3 ^ 40 * 2897692 * 2
def baseEnd_2897692 : Nat := 495969594896060666807921

theorem tailTrace_2897692 : CollatzResearch.WordTrace tailWord_2897692 prefixEnd_2897692 495969594896060666807921 := by
  unfold tailWord_2897692
  simp only [CollatzResearch.WordTrace]
  refine ⟨52843754909082122619395665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70458339878776163492527553 52843754909082122619395665)
  ·
    refine ⟨39632816181811591964546749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52843754909082122619395665 39632816181811591964546749)
    ·
      refine ⟨14862306068179346986705031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39632816181811591964546749 14862306068179346986705031)
      ·
        refine ⟨22293459102269020480057547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14862306068179346986705031 22293459102269020480057547)
        ·
          refine ⟨33440188653403530720086321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22293459102269020480057547 33440188653403530720086321)
          ·
            refine ⟨25080141490052648040064741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33440188653403530720086321 25080141490052648040064741)
            ·
              refine ⟨4702526529384871507512139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25080141490052648040064741 4702526529384871507512139)
              ·
                refine ⟨7053789794077307261268209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702526529384871507512139 7053789794077307261268209)
                ·
                  refine ⟨5290342345557980445951157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7053789794077307261268209 5290342345557980445951157)
                  ·
                    refine ⟨495969594896060666807921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5290342345557980445951157 495969594896060666807921)
                    ·
                      rfl

theorem cell23_2897692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2897692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897692 prefixEnd_2897692 := by exact prefixLift 2897692
  have htrace : WordTrace (prefixWord ++ tailWord_2897692) baseStart_2897692 baseEnd_2897692 := by
    simpa [prefixWord, tailWord_2897692, baseEnd_2897692] using wordTrace_append hprefix tailTrace_2897692
  have hstable : (prefixWord ++ tailWord_2897692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897692).length < 2 ^ (prefixWord ++ tailWord_2897692).sum := by decide
  have hdescent : baseEnd_2897692 < baseStart_2897692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897749 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2897749 : Nat := 118140960795 + 2897749 * 2 ^ 59
def prefixEnd_2897749 : Nat := 4983230072969 + 3 ^ 40 * 2897749 * 2
def baseEnd_2897749 : Nat := 1487938053085488277411001

theorem tailTrace_2897749 : CollatzResearch.WordTrace tailWord_2897749 prefixEnd_2897749 1487938053085488277411001 := by
  unfold tailWord_2897749
  simp only [CollatzResearch.WordTrace]
  refine ⟨105689588778957743973616301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70459725852638495982410867 105689588778957743973616301)
  ·
    refine ⟨39633595792109153990106113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105689588778957743973616301 39633595792109153990106113)
    ·
      refine ⟨29725196844081865492579585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39633595792109153990106113 29725196844081865492579585)
      ·
        refine ⟨22293897633061399119434689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29725196844081865492579585 22293897633061399119434689)
        ·
          refine ⟨16720423224796049339576017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22293897633061399119434689 16720423224796049339576017)
          ·
            refine ⟨12540317418597037004682013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16720423224796049339576017 12540317418597037004682013)
            ·
              refine ⟨4702619031973888876755755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12540317418597037004682013 4702619031973888876755755)
              ·
                refine ⟨7053928547960833315133633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4702619031973888876755755 7053928547960833315133633)
                ·
                  refine ⟨5290446410970624986350225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7053928547960833315133633 5290446410970624986350225)
                  ·
                    refine ⟨3967834808227968739762669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5290446410970624986350225 3967834808227968739762669)
                    ·
                      refine ⟨1487938053085488277411001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3967834808227968739762669 1487938053085488277411001)
                      ·
                        rfl

theorem cell23_2897749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2897749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897749 prefixEnd_2897749 := by exact prefixLift 2897749
  have htrace : WordTrace (prefixWord ++ tailWord_2897749) baseStart_2897749 baseEnd_2897749 := by
    simpa [prefixWord, tailWord_2897749, baseEnd_2897749] using wordTrace_append hprefix tailTrace_2897749
  have hstable : (prefixWord ++ tailWord_2897749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897749).length < 2 ^ (prefixWord ++ tailWord_2897749).sum := by decide
  have hdescent : baseEnd_2897749 < baseStart_2897749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897835 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_2897835 : Nat := 118140960795 + 2897835 * 2 ^ 59
def prefixEnd_2897835 : Nat := 4983230072969 + 3 ^ 40 * 2897835 * 2
def baseEnd_2897835 : Nat := 1487982212421774940935605

theorem tailTrace_2897835 : CollatzResearch.WordTrace tailWord_2897835 prefixEnd_2897835 1487982212421774940935605 := by
  unfold tailWord_2897835
  simp only [CollatzResearch.WordTrace]
  refine ⟨105692725456646180661246959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70461816971097453774164639 105692725456646180661246959)
  ·
    refine ⟨158539088184969270991870439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105692725456646180661246959 158539088184969270991870439)
    ·
      refine ⟨237808632277453906487805659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158539088184969270991870439 237808632277453906487805659)
      ·
        refine ⟨356712948416180859731708489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237808632277453906487805659 356712948416180859731708489)
        ·
          refine ⟨267534711312135644798781367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356712948416180859731708489 267534711312135644798781367)
          ·
            refine ⟨401302066968203467198172051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267534711312135644798781367 401302066968203467198172051)
            ·
              refine ⟨601953100452305200797258077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401302066968203467198172051 601953100452305200797258077)
              ·
                refine ⟨225732412669614450298971779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601953100452305200797258077 225732412669614450298971779)
                ·
                  refine ⟨338598619004421675448457669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225732412669614450298971779 338598619004421675448457669)
                  ·
                    refine ⟨63487241063329064146585813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338598619004421675448457669 63487241063329064146585813)
                    ·
                      refine ⟨1487982212421774940935605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63487241063329064146585813 1487982212421774940935605)
                      ·
                        rfl

theorem cell23_2897835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_2897835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897835 prefixEnd_2897835 := by exact prefixLift 2897835
  have htrace : WordTrace (prefixWord ++ tailWord_2897835) baseStart_2897835 baseEnd_2897835 := by
    simpa [prefixWord, tailWord_2897835, baseEnd_2897835] using wordTrace_append hprefix tailTrace_2897835
  have hstable : (prefixWord ++ tailWord_2897835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897835).length < 2 ^ (prefixWord ++ tailWord_2897835).sum := by decide
  have hdescent : baseEnd_2897835 < baseStart_2897835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897887 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 1, 2, 2]
def baseStart_2897887 : Nat := 118140960795 + 2897887 * 2 ^ 59
def prefixEnd_2897887 : Nat := 4983230072969 + 3 ^ 40 * 2897887 * 2
def baseEnd_2897887 : Nat := 1488008913415808737485367

theorem tailTrace_2897887 : CollatzResearch.WordTrace tailWord_2897887 prefixEnd_2897887 1488008913415808737485367 := by
  unfold tailWord_2897887
  simp only [CollatzResearch.WordTrace]
  refine ⟨105694622052457793542139915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70463081368305195694759943 105694622052457793542139915)
  ·
    refine ⟨158541933078686690313209873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105694622052457793542139915 158541933078686690313209873)
    ·
      refine ⟨118906449809015017734907405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158541933078686690313209873 118906449809015017734907405)
      ·
        refine ⟨44589918678380631650590277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118906449809015017734907405 44589918678380631650590277)
        ·
          refine ⟨8360609752196368434485677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44589918678380631650590277 8360609752196368434485677)
          ·
            refine ⟨3135228657073638162932129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8360609752196368434485677 3135228657073638162932129)
            ·
              refine ⟨2351421492805228622199097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3135228657073638162932129 2351421492805228622199097)
              ·
                refine ⟨1763566119603921466649323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2351421492805228622199097 1763566119603921466649323)
                ·
                  refine ⟨2645349179405882199973985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763566119603921466649323 2645349179405882199973985)
                  ·
                    refine ⟨1984011884554411649980489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2645349179405882199973985 1984011884554411649980489)
                    ·
                      refine ⟨1488008913415808737485367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1984011884554411649980489 1488008913415808737485367)
                      ·
                        rfl

theorem cell23_2897887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_2897887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897887 prefixEnd_2897887 := by exact prefixLift 2897887
  have htrace : WordTrace (prefixWord ++ tailWord_2897887) baseStart_2897887 baseEnd_2897887 := by
    simpa [prefixWord, tailWord_2897887, baseEnd_2897887] using wordTrace_append hprefix tailTrace_2897887
  have hstable : (prefixWord ++ tailWord_2897887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897887).length < 2 ^ (prefixWord ++ tailWord_2897887).sum := by decide
  have hdescent : baseEnd_2897887 < baseStart_2897887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897892 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2897892 : Nat := 118140960795 + 2897892 * 2 ^ 59
def prefixEnd_2897892 : Nat := 4983230072969 + 3 ^ 40 * 2897892 * 2
def baseEnd_2897892 : Nat := 1488011480819081217922843

theorem tailTrace_2897892 : CollatzResearch.WordTrace tailWord_2897892 prefixEnd_2897892 1488011480819081217922843 := by
  unfold tailWord_2897892
  simp only [CollatzResearch.WordTrace]
  refine ⟨52847402208719839698035965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70463202944959786264047953 52847402208719839698035965)
  ·
    refine ⟨19817775828269939886763487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52847402208719839698035965 19817775828269939886763487)
    ·
      refine ⟨29726663742404909830145231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19817775828269939886763487 29726663742404909830145231)
      ·
        refine ⟨44589995613607364745217847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29726663742404909830145231 44589995613607364745217847)
        ·
          refine ⟨66884993420411047117826771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44589995613607364745217847 66884993420411047117826771)
          ·
            refine ⟨100327490130616570676740157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66884993420411047117826771 100327490130616570676740157)
            ·
              refine ⟨37622808798981214003777559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100327490130616570676740157 37622808798981214003777559)
              ·
                refine ⟨56434213198471821005666339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37622808798981214003777559 56434213198471821005666339)
                ·
                  refine ⟨84651319797707731508499509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56434213198471821005666339 84651319797707731508499509)
                  ·
                    refine ⟨7936061231035099828921829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84651319797707731508499509 7936061231035099828921829)
                    ·
                      refine ⟨1488011480819081217922843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7936061231035099828921829 1488011480819081217922843)
                      ·
                        rfl

theorem cell23_2897892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2897892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897892 prefixEnd_2897892 := by exact prefixLift 2897892
  have htrace : WordTrace (prefixWord ++ tailWord_2897892) baseStart_2897892 baseEnd_2897892 := by
    simpa [prefixWord, tailWord_2897892, baseEnd_2897892] using wordTrace_append hprefix tailTrace_2897892
  have hstable : (prefixWord ++ tailWord_2897892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897892).length < 2 ^ (prefixWord ++ tailWord_2897892).sum := by decide
  have hdescent : baseEnd_2897892 < baseStart_2897892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897912 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_2897912 : Nat := 118140960795 + 2897912 * 2 ^ 59
def prefixEnd_2897912 : Nat := 4983230072969 + 3 ^ 40 * 2897912 * 2
def baseEnd_2897912 : Nat := 1488021750432171139672751

theorem tailTrace_2897912 : CollatzResearch.WordTrace tailWord_2897912 prefixEnd_2897912 1488021750432171139672751 := by
  unfold tailWord_2897912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52847766938683611405899995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70463689251578148541199993 52847766938683611405899995)
  ·
    refine ⟨79271650408025417108849993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52847766938683611405899995 79271650408025417108849993)
    ·
      refine ⟨59453737806019062831637495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79271650408025417108849993 59453737806019062831637495)
      ·
        refine ⟨89180606709028594247456243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59453737806019062831637495 89180606709028594247456243)
        ·
          refine ⟨133770910063542891371184365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89180606709028594247456243 133770910063542891371184365)
          ·
            refine ⟨50164091273828584264194137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133770910063542891371184365 50164091273828584264194137)
            ·
              refine ⟨37623068455371438198145603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50164091273828584264194137 37623068455371438198145603)
              ·
                refine ⟨56434602683057157297218405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37623068455371438198145603 56434602683057157297218405)
                ·
                  refine ⟨10581488003073216993228451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56434602683057157297218405 10581488003073216993228451)
                  ·
                    refine ⟨15872232004609825489842677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10581488003073216993228451 15872232004609825489842677)
                    ·
                      refine ⟨1488021750432171139672751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15872232004609825489842677 1488021750432171139672751)
                      ·
                        rfl

theorem cell23_2897912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_2897912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897912 prefixEnd_2897912 := by exact prefixLift 2897912
  have htrace : WordTrace (prefixWord ++ tailWord_2897912) baseStart_2897912 baseEnd_2897912 := by
    simpa [prefixWord, tailWord_2897912, baseEnd_2897912] using wordTrace_append hprefix tailTrace_2897912
  have hstable : (prefixWord ++ tailWord_2897912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897912).length < 2 ^ (prefixWord ++ tailWord_2897912).sum := by decide
  have hdescent : baseEnd_2897912 < baseStart_2897912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897932 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 9]
def baseStart_2897932 : Nat := 118140960795 + 2897932 * 2 ^ 59
def prefixEnd_2897932 : Nat := 4983230072969 + 3 ^ 40 * 2897932 * 2
def baseEnd_2897932 : Nat := 165336891116140117935851

theorem tailTrace_2897932 : CollatzResearch.WordTrace tailWord_2897932 prefixEnd_2897932 165336891116140117935851 := by
  unfold tailWord_2897932
  simp only [CollatzResearch.WordTrace]
  refine ⟨52848131668647383113764025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70464175558196510818352033 52848131668647383113764025)
  ·
    refine ⟨39636098751485537335323019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52848131668647383113764025 39636098751485537335323019)
    ·
      refine ⟨59454148127228306002984529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39636098751485537335323019 59454148127228306002984529)
      ·
        refine ⟨44590611095421229502238397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59454148127228306002984529 44590611095421229502238397)
        ·
          refine ⟨16721479160782961063339399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44590611095421229502238397 16721479160782961063339399)
          ·
            refine ⟨25082218741174441595009099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16721479160782961063339399 25082218741174441595009099)
            ·
              refine ⟨37623328111761662392513649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25082218741174441595009099 37623328111761662392513649)
              ·
                refine ⟨28217496083821246794385237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37623328111761662392513649 28217496083821246794385237)
                ·
                  refine ⟨165336891116140117935851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28217496083821246794385237 165336891116140117935851)
                  ·
                    rfl

theorem cell23_2897932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_2897932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897932 prefixEnd_2897932 := by exact prefixLift 2897932
  have htrace : WordTrace (prefixWord ++ tailWord_2897932) baseStart_2897932 baseEnd_2897932 := by
    simpa [prefixWord, tailWord_2897932, baseEnd_2897932] using wordTrace_append hprefix tailTrace_2897932
  have hstable : (prefixWord ++ tailWord_2897932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897932).length < 2 ^ (prefixWord ++ tailWord_2897932).sum := by decide
  have hdescent : baseEnd_2897932 < baseStart_2897932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897949 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 7]
def baseStart_2897949 : Nat := 118140960795 + 2897949 * 2 ^ 59
def prefixEnd_2897949 : Nat := 4983230072969 + 3 ^ 40 * 2897949 * 2
def baseEnd_2897949 : Nat := 165337861024043054990009

theorem tailTrace_2897949 : CollatzResearch.WordTrace tailWord_2897949 prefixEnd_2897949 165337861024043054990009 := by
  unfold tailWord_2897949
  simp only [CollatzResearch.WordTrace]
  refine ⟨105696883378233178130896901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70464588918822118753931267 105696883378233178130896901)
  ·
    refine ⟨19818165633418720899543169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105696883378233178130896901 19818165633418720899543169)
    ·
      refine ⟨14863624225064040674657377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19818165633418720899543169 14863624225064040674657377)
      ·
        refine ⟨11147718168798030505993033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14863624225064040674657377 11147718168798030505993033)
        ·
          refine ⟨8360788626598522879494775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11147718168798030505993033 8360788626598522879494775)
          ·
            refine ⟨12541182939897784319242163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360788626598522879494775 12541182939897784319242163)
            ·
              refine ⟨18811774409846676478863245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12541182939897784319242163 18811774409846676478863245)
              ·
                refine ⟨7054415403692503679573717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18811774409846676478863245 7054415403692503679573717)
                ·
                  refine ⟨165337861024043054990009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7054415403692503679573717 165337861024043054990009)
                  ·
                    rfl

theorem cell23_2897949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_2897949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897949 prefixEnd_2897949 := by exact prefixLift 2897949
  have htrace : WordTrace (prefixWord ++ tailWord_2897949) baseStart_2897949 baseEnd_2897949 := by
    simpa [prefixWord, tailWord_2897949, baseEnd_2897949] using wordTrace_append hprefix tailTrace_2897949
  have hstable : (prefixWord ++ tailWord_2897949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897949).length < 2 ^ (prefixWord ++ tailWord_2897949).sum := by decide
  have hdescent : baseEnd_2897949 < baseStart_2897949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2897999 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_2897999 : Nat := 118140960795 + 2897999 * 2 ^ 59
def prefixEnd_2897999 : Nat := 4983230072969 + 3 ^ 40 * 2897999 * 2
def baseEnd_2897999 : Nat := 1488066423249112299284851

theorem tailTrace_2897999 : CollatzResearch.WordTrace tailWord_2897999 prefixEnd_2897999 1488066423249112299284851 := by
  unfold tailWord_2897999
  simp only [CollatzResearch.WordTrace]
  refine ⟨105698707028052036670217051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70465804685368024446811367 105698707028052036670217051)
  ·
    refine ⟨158548060542078055005325577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105698707028052036670217051 158548060542078055005325577)
    ·
      refine ⟨118911045406558541253994183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158548060542078055005325577 118911045406558541253994183)
      ·
        refine ⟨178366568109837811880991275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118911045406558541253994183 178366568109837811880991275)
        ·
          refine ⟨267549852164756717821486913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178366568109837811880991275 267549852164756717821486913)
          ·
            refine ⟨200662389123567538366115185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267549852164756717821486913 200662389123567538366115185)
            ·
              refine ⟨150496791842675653774586389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200662389123567538366115185 150496791842675653774586389)
              ·
                refine ⟨7054537117625421270683737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150496791842675653774586389 7054537117625421270683737)
                ·
                  refine ⟨5290902838219065953012803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7054537117625421270683737 5290902838219065953012803)
                  ·
                    refine ⟨7936354257328598929519205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5290902838219065953012803 7936354257328598929519205)
                    ·
                      refine ⟨1488066423249112299284851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7936354257328598929519205 1488066423249112299284851)
                      ·
                        rfl

theorem cell23_2897999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_2897999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2897999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2897999 prefixEnd_2897999 := by exact prefixLift 2897999
  have htrace : WordTrace (prefixWord ++ tailWord_2897999) baseStart_2897999 baseEnd_2897999 := by
    simpa [prefixWord, tailWord_2897999, baseEnd_2897999] using wordTrace_append hprefix tailTrace_2897999
  have hstable : (prefixWord ++ tailWord_2897999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2897999).length < 2 ^ (prefixWord ++ tailWord_2897999).sum := by decide
  have hdescent : baseEnd_2897999 < baseStart_2897999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2897999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898019 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2898019 : Nat := 118140960795 + 2898019 * 2 ^ 59
def prefixEnd_2898019 : Nat := 4983230072969 + 3 ^ 40 * 2898019 * 2
def baseEnd_2898019 : Nat := 1488076692862202221034759

theorem tailTrace_2898019 : CollatzResearch.WordTrace tailWord_2898019 prefixEnd_2898019 1488076692862202221034759 := by
  unfold tailWord_2898019
  simp only [CollatzResearch.WordTrace]
  refine ⟨105699436487979580085945111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70466290991986386723963407 105699436487979580085945111)
  ·
    refine ⟨158549154731969370128917667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105699436487979580085945111 158549154731969370128917667)
    ·
      refine ⟨237823732097954055193376501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158549154731969370128917667 237823732097954055193376501)
      ·
        refine ⟨22295974884183192674379047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237823732097954055193376501 22295974884183192674379047)
        ·
          refine ⟨33443962326274789011568571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22295974884183192674379047 33443962326274789011568571)
          ·
            refine ⟨50165943489412183517352857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33443962326274789011568571 50165943489412183517352857)
            ·
              refine ⟨37624457617059137638014643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50165943489412183517352857 37624457617059137638014643)
              ·
                refine ⟨56436686425588706457021965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37624457617059137638014643 56436686425588706457021965)
                ·
                  refine ⟨21163757409595764921383237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56436686425588706457021965 21163757409595764921383237)
                  ·
                    refine ⟨3968204514299205922759357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21163757409595764921383237 3968204514299205922759357)
                    ·
                      refine ⟨1488076692862202221034759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3968204514299205922759357 1488076692862202221034759)
                      ·
                        rfl

theorem cell23_2898019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2898019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898019 prefixEnd_2898019 := by exact prefixLift 2898019
  have htrace : WordTrace (prefixWord ++ tailWord_2898019) baseStart_2898019 baseEnd_2898019 := by
    simpa [prefixWord, tailWord_2898019, baseEnd_2898019] using wordTrace_append hprefix tailTrace_2898019
  have hstable : (prefixWord ++ tailWord_2898019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898019).length < 2 ^ (prefixWord ++ tailWord_2898019).sum := by decide
  have hdescent : baseEnd_2898019 < baseStart_2898019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898056 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 6]
def baseStart_2898056 : Nat := 118140960795 + 2898056 * 2 ^ 59
def prefixEnd_2898056 : Nat := 4983230072969 + 3 ^ 40 * 2898056 * 2
def baseEnd_2898056 : Nat := 165343965738490952919121

theorem tailTrace_2898056 : CollatzResearch.WordTrace tailWord_2898056 prefixEnd_2898056 165343965738490952919121 := by
  unfold tailWord_2898056
  simp only [CollatzResearch.WordTrace]
  refine ⟨52850392994422767702521011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70467190659230356936694681 52850392994422767702521011)
  ·
    refine ⟨79275589491634151553781517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52850392994422767702521011 79275589491634151553781517)
    ·
      refine ⟨29728346059362806832668069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79275589491634151553781517 29728346059362806832668069)
      ·
        refine ⟨5574064886130526281125263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29728346059362806832668069 5574064886130526281125263)
        ·
          refine ⟨8361097329195789421687895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574064886130526281125263 8361097329195789421687895)
          ·
            refine ⟨12541645993793684132531843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361097329195789421687895 12541645993793684132531843)
            ·
              refine ⟨18812468990690526198797765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12541645993793684132531843 18812468990690526198797765)
              ·
                refine ⟨3527337935754473662274581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18812468990690526198797765 3527337935754473662274581)
                ·
                  refine ⟨165343965738490952919121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3527337935754473662274581 165343965738490952919121)
                  ·
                    rfl

theorem cell23_2898056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 6].length) (baseStart_2898056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898056 prefixEnd_2898056 := by exact prefixLift 2898056
  have htrace : WordTrace (prefixWord ++ tailWord_2898056) baseStart_2898056 baseEnd_2898056 := by
    simpa [prefixWord, tailWord_2898056, baseEnd_2898056] using wordTrace_append hprefix tailTrace_2898056
  have hstable : (prefixWord ++ tailWord_2898056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898056).length < 2 ^ (prefixWord ++ tailWord_2898056).sum := by decide
  have hdescent : baseEnd_2898056 < baseStart_2898056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898069 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2898069 : Nat := 118140960795 + 2898069 * 2 ^ 59
def prefixEnd_2898069 : Nat := 4983230072969 + 3 ^ 40 * 2898069 * 2
def baseEnd_2898069 : Nat := 496034122298309008469843

theorem tailTrace_2898069 : CollatzResearch.WordTrace tailWord_2898069 prefixEnd_2898069 496034122298309008469843 := by
  unfold tailWord_2898069
  simp only [CollatzResearch.WordTrace]
  refine ⟨105701260137798438625265261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70467506758532292416843507 105701260137798438625265261)
  ·
    refine ⟨39637972551674414484474473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105701260137798438625265261 39637972551674414484474473)
    ·
      refine ⟨29728479413755810863355855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39637972551674414484474473 29728479413755810863355855)
      ·
        refine ⟨44592719120633716295033783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29728479413755810863355855 44592719120633716295033783)
        ·
          refine ⟨66889078680950574442550675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44592719120633716295033783 66889078680950574442550675)
          ·
            refine ⟨100333618021425861663826013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66889078680950574442550675 100333618021425861663826013)
            ·
              refine ⟨37625106758034698123934755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100333618021425861663826013 37625106758034698123934755)
              ·
                refine ⟨56437660137052047185902133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37625106758034698123934755 56437660137052047185902133)
                ·
                  refine ⟨5291030637848629423678325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56437660137052047185902133 5291030637848629423678325)
                  ·
                    refine ⟨496034122298309008469843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5291030637848629423678325 496034122298309008469843)
                    ·
                      rfl

theorem cell23_2898069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2898069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898069 prefixEnd_2898069 := by exact prefixLift 2898069
  have htrace : WordTrace (prefixWord ++ tailWord_2898069) baseStart_2898069 baseEnd_2898069 := by
    simpa [prefixWord, tailWord_2898069, baseEnd_2898069] using wordTrace_append hprefix tailTrace_2898069
  have hstable : (prefixWord ++ tailWord_2898069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898069).length < 2 ^ (prefixWord ++ tailWord_2898069).sum := by decide
  have hdescent : baseEnd_2898069 < baseStart_2898069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898087 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2898087 : Nat := 118140960795 + 2898087 * 2 ^ 59
def prefixEnd_2898087 : Nat := 4983230072969 + 3 ^ 40 * 2898087 * 2
def baseEnd_2898087 : Nat := 1488111609546707954984447

theorem tailTrace_2898087 : CollatzResearch.WordTrace tailWord_2898087 prefixEnd_2898087 1488111609546707954984447 := by
  unfold tailWord_2898087
  simp only [CollatzResearch.WordTrace]
  refine ⟨105701916651733227699420515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70467944434488818466280343 105701916651733227699420515)
  ·
    refine ⟨158552874977599841549130773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105701916651733227699420515 158552874977599841549130773)
    ·
      refine ⟨7432166014574992572615505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158552874977599841549130773 7432166014574992572615505)
      ·
        refine ⟨5574124510931244429461629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7432166014574992572615505 5574124510931244429461629)
        ·
          refine ⟨2090296691599216661048111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5574124510931244429461629 2090296691599216661048111)
          ·
            refine ⟨3135445037398824991572167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090296691599216661048111 3135445037398824991572167)
            ·
              refine ⟨4703167556098237487358251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135445037398824991572167 4703167556098237487358251)
              ·
                refine ⟨7054751334147356231037377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4703167556098237487358251 7054751334147356231037377)
                ·
                  refine ⟨5291063500610517173278033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7054751334147356231037377 5291063500610517173278033)
                  ·
                    refine ⟨3968297625457887879958525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5291063500610517173278033 3968297625457887879958525)
                    ·
                      refine ⟨1488111609546707954984447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3968297625457887879958525 1488111609546707954984447)
                      ·
                        rfl

theorem cell23_2898087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2898087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898087 prefixEnd_2898087 := by exact prefixLift 2898087
  have htrace : WordTrace (prefixWord ++ tailWord_2898087) baseStart_2898087 baseEnd_2898087 := by
    simpa [prefixWord, tailWord_2898087, baseEnd_2898087] using wordTrace_append hprefix tailTrace_2898087
  have hstable : (prefixWord ++ tailWord_2898087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898087).length < 2 ^ (prefixWord ++ tailWord_2898087).sum := by decide
  have hdescent : baseEnd_2898087 < baseStart_2898087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898094 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2898094 : Nat := 118140960795 + 2898094 * 2 ^ 59
def prefixEnd_2898094 : Nat := 4983230072969 + 3 ^ 40 * 2898094 * 2
def baseEnd_2898094 : Nat := 496038401303763142532305

theorem tailTrace_2898094 : CollatzResearch.WordTrace tailWord_2898094 prefixEnd_2898094 496038401303763142532305 := by
  unfold tailWord_2898094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212771495338483486865667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70468114641805245263283557 13212771495338483486865667)
  ·
    refine ⟨19819157243007725230298501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13212771495338483486865667 19819157243007725230298501)
    ·
      refine ⟨3716091983063948480680969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19819157243007725230298501 3716091983063948480680969)
      ·
        refine ⟨2787068987297961360510727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3716091983063948480680969 2787068987297961360510727)
        ·
          refine ⟨4180603480946942040766091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787068987297961360510727 4180603480946942040766091)
          ·
            refine ⟨6270905221420413061149137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180603480946942040766091 6270905221420413061149137)
            ·
              refine ⟨4703178916065309795861853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270905221420413061149137 4703178916065309795861853)
              ·
                refine ⟨1763692093524491173448195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4703178916065309795861853 1763692093524491173448195)
                ·
                  refine ⟨2645538140286736760172293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1763692093524491173448195 2645538140286736760172293)
                  ·
                    refine ⟨496038401303763142532305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2645538140286736760172293 496038401303763142532305)
                    ·
                      rfl

theorem cell23_2898094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2898094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898094 prefixEnd_2898094 := by exact prefixLift 2898094
  have htrace : WordTrace (prefixWord ++ tailWord_2898094) baseStart_2898094 baseEnd_2898094 := by
    simpa [prefixWord, tailWord_2898094, baseEnd_2898094] using wordTrace_append hprefix tailTrace_2898094
  have hstable : (prefixWord ++ tailWord_2898094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898094).length < 2 ^ (prefixWord ++ tailWord_2898094).sum := by decide
  have hdescent : baseEnd_2898094 < baseStart_2898094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898103 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 1, 5]
def baseStart_2898103 : Nat := 118140960795 + 2898103 * 2 ^ 59
def prefixEnd_2898103 : Nat := 4983230072969 + 3 ^ 40 * 2898103 * 2
def baseEnd_2898103 : Nat := 496039941745726630794791

theorem tailTrace_2898103 : CollatzResearch.WordTrace tailWord_2898103 prefixEnd_2898103 496039941745726630794791 := by
  unfold tailWord_2898103
  simp only [CollatzResearch.WordTrace]
  refine ⟨105702500219675262432002963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70468333479783508288001975 105702500219675262432002963)
  ·
    refine ⟨158553750329512893648004445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105702500219675262432002963 158553750329512893648004445)
    ·
      refine ⟨59457656373567335118001667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158553750329512893648004445 59457656373567335118001667)
      ·
        refine ⟨89186484560351002677002501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59457656373567335118001667 89186484560351002677002501)
        ·
          refine ⟨16722465855065813001937969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89186484560351002677002501 16722465855065813001937969)
          ·
            refine ⟨12541849391299359751453477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16722465855065813001937969 12541849391299359751453477)
            ·
              refine ⟨2351596760868629953397527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12541849391299359751453477 2351596760868629953397527)
              ·
                refine ⟨3527395141302944930096291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2351596760868629953397527 3527395141302944930096291)
                ·
                  refine ⟨5291092711954417395144437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3527395141302944930096291 5291092711954417395144437)
                  ·
                    refine ⟨496039941745726630794791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5291092711954417395144437 496039941745726630794791)
                    ·
                      rfl

theorem cell23_2898103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_2898103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898103 prefixEnd_2898103 := by exact prefixLift 2898103
  have htrace : WordTrace (prefixWord ++ tailWord_2898103) baseStart_2898103 baseEnd_2898103 := by
    simpa [prefixWord, tailWord_2898103, baseEnd_2898103] using wordTrace_append hprefix tailTrace_2898103
  have hstable : (prefixWord ++ tailWord_2898103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898103).length < 2 ^ (prefixWord ++ tailWord_2898103).sum := by decide
  have hdescent : baseEnd_2898103 < baseStart_2898103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898119 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_2898119 : Nat := 118140960795 + 2898119 * 2 ^ 59
def prefixEnd_2898119 : Nat := 4983230072969 + 3 ^ 40 * 2898119 * 2
def baseEnd_2898119 : Nat := 1488128040927651829784299

theorem tailTrace_2898119 : CollatzResearch.WordTrace tailWord_2898119 prefixEnd_2898119 1488128040927651829784299 := by
  unfold tailWord_2898119
  simp only [CollatzResearch.WordTrace]
  refine ⟨105703083787617297164585411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70468722525078198109723607 105703083787617297164585411)
  ·
    refine ⟨158554625681425945746878117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105703083787617297164585411 158554625681425945746878117)
    ·
      refine ⟨29728992315267364827539647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158554625681425945746878117 29728992315267364827539647)
      ·
        refine ⟨44593488472901047241309471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29728992315267364827539647 44593488472901047241309471)
        ·
          refine ⟨66890232709351570861964207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44593488472901047241309471 66890232709351570861964207)
          ·
            refine ⟨100335349064027356292946311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66890232709351570861964207 100335349064027356292946311)
            ·
              refine ⟨150503023596041034439419467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100335349064027356292946311 150503023596041034439419467)
              ·
                refine ⟨225754535394061551659129201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150503023596041034439419467 225754535394061551659129201)
                ·
                  refine ⟨169315901545546163744346901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225754535394061551659129201 169315901545546163744346901)
                  ·
                    refine ⟨7936682884947476425516261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 169315901545546163744346901 7936682884947476425516261)
                    ·
                      refine ⟨1488128040927651829784299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7936682884947476425516261 1488128040927651829784299)
                      ·
                        rfl

theorem cell23_2898119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_2898119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898119 prefixEnd_2898119 := by exact prefixLift 2898119
  have htrace : WordTrace (prefixWord ++ tailWord_2898119) baseStart_2898119 baseEnd_2898119 := by
    simpa [prefixWord, tailWord_2898119, baseEnd_2898119] using wordTrace_append hprefix tailTrace_2898119
  have hstable : (prefixWord ++ tailWord_2898119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898119).length < 2 ^ (prefixWord ++ tailWord_2898119).sum := by decide
  have hdescent : baseEnd_2898119 < baseStart_2898119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898126 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2898126 : Nat := 118140960795 + 2898126 * 2 ^ 59
def prefixEnd_2898126 : Nat := 4983230072969 + 3 ^ 40 * 2898126 * 2
def baseEnd_2898126 : Nat := 1488131635292233302396767

theorem tailTrace_2898126 : CollatzResearch.WordTrace tailWord_2898126 prefixEnd_2898126 1488131635292233302396767 := by
  unfold tailWord_2898126
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212917387323992170011279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70468892732394624906726821 13212917387323992170011279)
  ·
    refine ⟨19819376080985988255016919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13212917387323992170011279 19819376080985988255016919)
    ·
      refine ⟨29729064121478982382525379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19819376080985988255016919 29729064121478982382525379)
      ·
        refine ⟨44593596182218473573788069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29729064121478982382525379 44593596182218473573788069)
        ·
          refine ⟨8361299284165963795085263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44593596182218473573788069 8361299284165963795085263)
          ·
            refine ⟨12541948926248945692627895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361299284165963795085263 12541948926248945692627895)
            ·
              refine ⟨18812923389373418538941843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12541948926248945692627895 18812923389373418538941843)
              ·
                refine ⟨28219385084060127808412765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18812923389373418538941843 28219385084060127808412765)
                ·
                  refine ⟨10582269406522547928154787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28219385084060127808412765 10582269406522547928154787)
                  ·
                    refine ⟨15873404109783821892232181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10582269406522547928154787 15873404109783821892232181)
                    ·
                      refine ⟨1488131635292233302396767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15873404109783821892232181 1488131635292233302396767)
                      ·
                        rfl

theorem cell23_2898126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2898126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898126 prefixEnd_2898126 := by exact prefixLift 2898126
  have htrace : WordTrace (prefixWord ++ tailWord_2898126) baseStart_2898126 baseEnd_2898126 := by
    simpa [prefixWord, tailWord_2898126, baseEnd_2898126] using wordTrace_append hprefix tailTrace_2898126
  have hstable : (prefixWord ++ tailWord_2898126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898126).length < 2 ^ (prefixWord ++ tailWord_2898126).sum := by decide
  have hdescent : baseEnd_2898126 < baseStart_2898126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898136 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2898136 : Nat := 118140960795 + 2898136 * 2 ^ 59
def prefixEnd_2898136 : Nat := 4983230072969 + 3 ^ 40 * 2898136 * 2
def baseEnd_2898136 : Nat := 1488136770098778263271721

theorem tailTrace_2898136 : CollatzResearch.WordTrace tailWord_2898136 prefixEnd_2898136 1488136770098778263271721 := by
  unfold tailWord_2898136
  simp only [CollatzResearch.WordTrace]
  refine ⟨52851851914277854533977131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70469135885703806045302841 52851851914277854533977131)
  ·
    refine ⟨79277777871416781800965697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52851851914277854533977131 79277777871416781800965697)
    ·
      refine ⟨59458333403562586350724273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79277777871416781800965697 59458333403562586350724273)
      ·
        refine ⟨44593750052671939763043205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59458333403562586350724273 44593750052671939763043205)
        ·
          refine ⟨8361328134875988705570601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44593750052671939763043205 8361328134875988705570601)
          ·
            refine ⟨6270996101156991529177951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8361328134875988705570601 6270996101156991529177951)
            ·
              refine ⟨9406494151735487293766927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270996101156991529177951 9406494151735487293766927)
              ·
                refine ⟨14109741227603230940650391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9406494151735487293766927 14109741227603230940650391)
                ·
                  refine ⟨21164611841404846410975587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14109741227603230940650391 21164611841404846410975587)
                  ·
                    refine ⟨31746917762107269616463381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21164611841404846410975587 31746917762107269616463381)
                    ·
                      refine ⟨1488136770098778263271721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31746917762107269616463381 1488136770098778263271721)
                      ·
                        rfl

theorem cell23_2898136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2898136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898136 prefixEnd_2898136 := by exact prefixLift 2898136
  have htrace : WordTrace (prefixWord ++ tailWord_2898136) baseStart_2898136 baseEnd_2898136 := by
    simpa [prefixWord, tailWord_2898136, baseEnd_2898136] using wordTrace_append hprefix tailTrace_2898136
  have hstable : (prefixWord ++ tailWord_2898136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898136).length < 2 ^ (prefixWord ++ tailWord_2898136).sum := by decide
  have hdescent : baseEnd_2898136 < baseStart_2898136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2898156 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_2898156 : Nat := 118140960795 + 2898156 * 2 ^ 59
def prefixEnd_2898156 : Nat := 4983230072969 + 3 ^ 40 * 2898156 * 2
def baseEnd_2898156 : Nat := 1488147039711868185021629

theorem tailTrace_2898156 : CollatzResearch.WordTrace tailWord_2898156 prefixEnd_2898156 1488147039711868185021629 := by
  unfold tailWord_2898156
  simp only [CollatzResearch.WordTrace]
  refine ⟨52852216644241626241841161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70469622192322168322454881 52852216644241626241841161)
  ·
    refine ⟨39639162483181219681380871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52852216644241626241841161 39639162483181219681380871)
    ·
      refine ⟨59458743724771829522071307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39639162483181219681380871 59458743724771829522071307)
      ·
        refine ⟨89188115587157744283106961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59458743724771829522071307 89188115587157744283106961)
        ·
          refine ⟨66891086690368308212330221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89188115587157744283106961 66891086690368308212330221)
          ·
            refine ⟨25084157508888115579623833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66891086690368308212330221 25084157508888115579623833)
            ·
              refine ⟨18813118131666086684717875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25084157508888115579623833 18813118131666086684717875)
              ·
                refine ⟨28219677197499130027076813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18813118131666086684717875 28219677197499130027076813)
                ·
                  refine ⟨10582378949062173760153805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28219677197499130027076813 10582378949062173760153805)
                  ·
                    refine ⟨3968392105898315160057677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10582378949062173760153805 3968392105898315160057677)
                    ·
                      refine ⟨1488147039711868185021629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3968392105898315160057677 1488147039711868185021629)
                      ·
                        rfl

theorem cell23_2898156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_2898156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2898156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2898156 prefixEnd_2898156 := by exact prefixLift 2898156
  have htrace : WordTrace (prefixWord ++ tailWord_2898156) baseStart_2898156 baseEnd_2898156 := by
    simpa [prefixWord, tailWord_2898156, baseEnd_2898156] using wordTrace_append hprefix tailTrace_2898156
  have hstable : (prefixWord ++ tailWord_2898156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2898156).length < 2 ^ (prefixWord ++ tailWord_2898156).sum := by decide
  have hdescent : baseEnd_2898156 < baseStart_2898156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2898156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
