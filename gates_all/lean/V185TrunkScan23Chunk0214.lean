import V185TrunkScan23Chunk0213

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1266352 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_1266352 : Nat := 118140960795 + 1266352 * 2 ^ 59
def prefixEnd_1266352 : Nat := 4983230072969 + 3 ^ 40 * 1266352 * 2
def baseEnd_1266352 : Nat := 650247253782534625676159

theorem tailTrace_1266352 : CollatzResearch.WordTrace tailWord_1266352 prefixEnd_1266352 650247253782534625676159 := by
  unfold tailWord_1266352
  simp only [CollatzResearch.WordTrace]
  refine ⟨23093825954115227274060655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30791767938820303032080873 23093825954115227274060655)
  ·
    refine ⟨34640738931172840911090983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23093825954115227274060655 34640738931172840911090983)
    ·
      refine ⟨51961108396759261366636475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34640738931172840911090983 51961108396759261366636475)
      ·
        refine ⟨77941662595138892049954713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51961108396759261366636475 77941662595138892049954713)
        ·
          refine ⟨58456246946354169037466035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77941662595138892049954713 58456246946354169037466035)
          ·
            refine ⟨87684370419531253556199053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58456246946354169037466035 87684370419531253556199053)
            ·
              refine ⟨32881638907324220083574645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87684370419531253556199053 32881638907324220083574645)
              ·
                refine ⟨3082653647561645632835123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32881638907324220083574645 3082653647561645632835123)
                ·
                  refine ⟨4623980471342468449252685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082653647561645632835123 4623980471342468449252685)
                  ·
                    refine ⟨1733992676753425668469757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4623980471342468449252685 1733992676753425668469757)
                    ·
                      refine ⟨650247253782534625676159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1733992676753425668469757 650247253782534625676159)
                      ·
                        rfl

theorem cell23_1266352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_1266352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266352 prefixEnd_1266352 := by exact prefixLift 1266352
  have htrace : WordTrace (prefixWord ++ tailWord_1266352) baseStart_1266352 baseEnd_1266352 := by
    simpa [prefixWord, tailWord_1266352, baseEnd_1266352] using wordTrace_append hprefix tailTrace_1266352
  have hstable : (prefixWord ++ tailWord_1266352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266352).length < 2 ^ (prefixWord ++ tailWord_1266352).sum := by decide
  have hdescent : baseEnd_1266352 < baseStart_1266352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266353 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1266353 : Nat := 118140960795 + 1266353 * 2 ^ 59
def prefixEnd_1266353 : Nat := 4983230072969 + 3 ^ 40 * 1266353 * 2
def baseEnd_1266353 : Nat := 650247767263189121763655

theorem tailTrace_1266353 : CollatzResearch.WordTrace tailWord_1266353 prefixEnd_1266353 650247767263189121763655 := by
  unfold tailWord_1266353
  simp only [CollatzResearch.WordTrace]
  refine ⟨46187688381226831718907713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30791792254151221145938475 46187688381226831718907713)
  ·
    refine ⟨34640766285920123789180785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46187688381226831718907713 34640766285920123789180785)
    ·
      refine ⟨25980574714440092841885589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34640766285920123789180785 25980574714440092841885589)
      ·
        refine ⟨1217839439739379351963387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25980574714440092841885589 1217839439739379351963387)
        ·
          refine ⟨1826759159609069027945081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217839439739379351963387 1826759159609069027945081)
          ·
            refine ⟨1370069369706801770958811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826759159609069027945081 1370069369706801770958811)
            ·
              refine ⟨2055104054560202656438217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370069369706801770958811 2055104054560202656438217)
              ·
                refine ⟨1541328040920151992328663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055104054560202656438217 1541328040920151992328663)
                ·
                  refine ⟨2311992061380227988492995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541328040920151992328663 2311992061380227988492995)
                  ·
                    refine ⟨3467988092070341982739493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311992061380227988492995 3467988092070341982739493)
                    ·
                      refine ⟨650247767263189121763655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3467988092070341982739493 650247767263189121763655)
                      ·
                        rfl

theorem cell23_1266353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1266353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266353 prefixEnd_1266353 := by exact prefixLift 1266353
  have htrace : WordTrace (prefixWord ++ tailWord_1266353) baseStart_1266353 baseEnd_1266353 := by
    simpa [prefixWord, tailWord_1266353, baseEnd_1266353] using wordTrace_append hprefix tailTrace_1266353
  have hstable : (prefixWord ++ tailWord_1266353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266353).length < 2 ^ (prefixWord ++ tailWord_1266353).sum := by decide
  have hdescent : baseEnd_1266353 < baseStart_1266353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266392 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1266392 : Nat := 118140960795 + 1266392 * 2 ^ 59
def prefixEnd_1266392 : Nat := 4983230072969 + 3 ^ 40 * 1266392 * 2
def baseEnd_1266392 : Nat := 650267793008714469175975

theorem tailTrace_1266392 : CollatzResearch.WordTrace tailWord_1266392 prefixEnd_1266392 650267793008714469175975 := by
  unfold tailWord_1266392
  simp only [CollatzResearch.WordTrace]
  refine ⟨23094555414042770689788715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30792740552057027586384953 23094555414042770689788715)
  ·
    refine ⟨34641833121064156034683073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23094555414042770689788715 34641833121064156034683073)
    ·
      refine ⟨25981374840798117026012305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34641833121064156034683073 25981374840798117026012305)
      ·
        refine ⟨19486031130598587769509229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25981374840798117026012305 19486031130598587769509229)
        ·
          refine ⟨7307261673974470413565961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19486031130598587769509229 7307261673974470413565961)
          ·
            refine ⟨5480446255480852810174471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7307261673974470413565961 5480446255480852810174471)
            ·
              refine ⟨8220669383221279215261707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480446255480852810174471 8220669383221279215261707)
              ·
                refine ⟨12331004074831918822892561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8220669383221279215261707 12331004074831918822892561)
                ·
                  refine ⟨9248253056123939117169421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12331004074831918822892561 9248253056123939117169421)
                  ·
                    refine ⟨3468094896046477168938533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9248253056123939117169421 3468094896046477168938533)
                    ·
                      refine ⟨650267793008714469175975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3468094896046477168938533 650267793008714469175975)
                      ·
                        rfl

theorem cell23_1266392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1266392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266392 prefixEnd_1266392 := by exact prefixLift 1266392
  have htrace : WordTrace (prefixWord ++ tailWord_1266392) baseStart_1266392 baseEnd_1266392 := by
    simpa [prefixWord, tailWord_1266392, baseEnd_1266392] using wordTrace_append hprefix tailTrace_1266392
  have hstable : (prefixWord ++ tailWord_1266392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266392).length < 2 ^ (prefixWord ++ tailWord_1266392).sum := by decide
  have hdescent : baseEnd_1266392 < baseStart_1266392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266409 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 1, 4, 2]
def baseStart_1266409 : Nat := 118140960795 + 1266409 * 2 ^ 59
def prefixEnd_1266409 : Nat := 4983230072969 + 3 ^ 40 * 1266409 * 2
def baseEnd_1266409 : Nat := 650276522179840902663397

theorem tailTrace_1266409 : CollatzResearch.WordTrace tailWord_1266409 prefixEnd_1266409 650276522179840902663397 := by
  unfold tailWord_1266409
  simp only [CollatzResearch.WordTrace]
  refine ⟨46189730869023953282946281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30793153912682635521964187 46189730869023953282946281)
  ·
    refine ⟨34642298151767964962209711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46189730869023953282946281 34642298151767964962209711)
    ·
      refine ⟨51963447227651947443314567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34642298151767964962209711 51963447227651947443314567)
      ·
        refine ⟨77945170841477921164971851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51963447227651947443314567 77945170841477921164971851)
        ·
          refine ⟨116917756262216881747457777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77945170841477921164971851 116917756262216881747457777)
          ·
            refine ⟨87688317196662661310593333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116917756262216881747457777 87688317196662661310593333)
            ·
              refine ⟨8220779737187124497868125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87688317196662661310593333 8220779737187124497868125)
              ·
                refine ⟨3082792401445171686700547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8220779737187124497868125 3082792401445171686700547)
                ·
                  refine ⟨4624188602167757530050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082792401445171686700547 4624188602167757530050821)
                  ·
                    refine ⟨867035362906454536884529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624188602167757530050821 867035362906454536884529)
                    ·
                      refine ⟨650276522179840902663397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867035362906454536884529 650276522179840902663397)
                      ·
                        rfl

theorem cell23_1266409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 4, 2].length) (baseStart_1266409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266409 prefixEnd_1266409 := by exact prefixLift 1266409
  have htrace : WordTrace (prefixWord ++ tailWord_1266409) baseStart_1266409 baseEnd_1266409 := by
    simpa [prefixWord, tailWord_1266409, baseEnd_1266409] using wordTrace_append hprefix tailTrace_1266409
  have hstable : (prefixWord ++ tailWord_1266409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266409).length < 2 ^ (prefixWord ++ tailWord_1266409).sum := by decide
  have hdescent : baseEnd_1266409 < baseStart_1266409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266412 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_1266412 : Nat := 118140960795 + 1266412 * 2 ^ 59
def prefixEnd_1266412 : Nat := 4983230072969 + 3 ^ 40 * 1266412 * 2
def baseEnd_1266412 : Nat := 650278062621804390925883

theorem tailTrace_1266412 : CollatzResearch.WordTrace tailWord_1266412 prefixEnd_1266412 650278062621804390925883 := by
  unfold tailWord_1266412
  simp only [CollatzResearch.WordTrace]
  refine ⟨23094920144006542397652745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30793226858675389863536993 23094920144006542397652745)
  ·
    refine ⟨17321190108004906798239559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23094920144006542397652745 17321190108004906798239559)
    ·
      refine ⟨25981785162007360197359339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17321190108004906798239559 25981785162007360197359339)
      ·
        refine ⟨38972677743011040296039009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25981785162007360197359339 38972677743011040296039009)
        ·
          refine ⟨29229508307258280222029257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38972677743011040296039009 29229508307258280222029257)
          ·
            refine ⟨21922131230443710166521943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29229508307258280222029257 21922131230443710166521943)
            ·
              refine ⟨32883196845665565249782915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21922131230443710166521943 32883196845665565249782915)
              ·
                refine ⟨49324795268498347874674373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32883196845665565249782915 49324795268498347874674373)
                ·
                  refine ⟨9248399112843440226501445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49324795268498347874674373 9248399112843440226501445)
                  ·
                    refine ⟨1734074833658145042469021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9248399112843440226501445 1734074833658145042469021)
                    ·
                      refine ⟨650278062621804390925883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734074833658145042469021 650278062621804390925883)
                      ·
                        rfl

theorem cell23_1266412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_1266412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266412 prefixEnd_1266412 := by exact prefixLift 1266412
  have htrace : WordTrace (prefixWord ++ tailWord_1266412) baseStart_1266412 baseEnd_1266412 := by
    simpa [prefixWord, tailWord_1266412, baseEnd_1266412] using wordTrace_append hprefix tailTrace_1266412
  have hstable : (prefixWord ++ tailWord_1266412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266412).length < 2 ^ (prefixWord ++ tailWord_1266412).sum := by decide
  have hdescent : baseEnd_1266412 < baseStart_1266412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266430 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_1266430 : Nat := 118140960795 + 1266430 * 2 ^ 59
def prefixEnd_1266430 : Nat := 4983230072969 + 3 ^ 40 * 1266430 * 2
def baseEnd_1266430 : Nat := 650287305273585320500801

theorem tailTrace_1266430 : CollatzResearch.WordTrace tailWord_1266430 prefixEnd_1266430 650287305273585320500801 := by
  unfold tailWord_1266430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773812100243484233682593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30793664534631915912973829 5773812100243484233682593)
  ·
    refine ⟨4330359075182613175261945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5773812100243484233682593 4330359075182613175261945)
    ·
      refine ⟨3247769306386959881446459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4330359075182613175261945 3247769306386959881446459)
      ·
        refine ⟨4871653959580439822169689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247769306386959881446459 4871653959580439822169689)
        ·
          refine ⟨3653740469685329866627267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871653959580439822169689 3653740469685329866627267)
          ·
            refine ⟨5480610704527994799940901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653740469685329866627267 5480610704527994799940901)
            ·
              refine ⟨1027614507098999024988919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5480610704527994799940901 1027614507098999024988919)
              ·
                refine ⟨1541421760648498537483379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027614507098999024988919 1541421760648498537483379)
                ·
                  refine ⟨2312132640972747806225069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541421760648498537483379 2312132640972747806225069)
                  ·
                    refine ⟨867049740364780427334401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312132640972747806225069 867049740364780427334401)
                    ·
                      refine ⟨650287305273585320500801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867049740364780427334401 650287305273585320500801)
                      ·
                        rfl

theorem cell23_1266430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_1266430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266430 prefixEnd_1266430 := by exact prefixLift 1266430
  have htrace : WordTrace (prefixWord ++ tailWord_1266430) baseStart_1266430 baseEnd_1266430 := by
    simpa [prefixWord, tailWord_1266430, baseEnd_1266430] using wordTrace_append hprefix tailTrace_1266430
  have hstable : (prefixWord ++ tailWord_1266430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266430).length < 2 ^ (prefixWord ++ tailWord_1266430).sum := by decide
  have hdescent : baseEnd_1266430 < baseStart_1266430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266439 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1266439 : Nat := 118140960795 + 1266439 * 2 ^ 59
def prefixEnd_1266439 : Nat := 4983230072969 + 3 ^ 40 * 1266439 * 2
def baseEnd_1266439 : Nat := 650291926599475785288259

theorem tailTrace_1266439 : CollatzResearch.WordTrace tailWord_1266439 prefixEnd_1266439 650291926599475785288259 := by
  unfold tailWord_1266439
  simp only [CollatzResearch.WordTrace]
  refine ⟨46190825058915268406538371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30793883372610178937692247 46190825058915268406538371)
  ·
    refine ⟨69286237588372902609807557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46190825058915268406538371 69286237588372902609807557)
    ·
      refine ⟨12991169547819919239338917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69286237588372902609807557 12991169547819919239338917)
      ·
        refine ⟨2435844290216234857376047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12991169547819919239338917 2435844290216234857376047)
        ·
          refine ⟨3653766435324352286064071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435844290216234857376047 3653766435324352286064071)
          ·
            refine ⟨5480649652986528429096107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653766435324352286064071 5480649652986528429096107)
            ·
              refine ⟨8220974479479792643644161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480649652986528429096107 8220974479479792643644161)
              ·
                refine ⟨6165730859609844482733121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8220974479479792643644161 6165730859609844482733121)
                ·
                  refine ⟨4624298144707383362049841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6165730859609844482733121 4624298144707383362049841)
                  ·
                    refine ⟨3468223608530537521537381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4624298144707383362049841 3468223608530537521537381)
                    ·
                      refine ⟨650291926599475785288259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3468223608530537521537381 650291926599475785288259)
                      ·
                        rfl

theorem cell23_1266439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1266439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266439 prefixEnd_1266439 := by exact prefixLift 1266439
  have htrace : WordTrace (prefixWord ++ tailWord_1266439) baseStart_1266439 baseEnd_1266439 := by
    simpa [prefixWord, tailWord_1266439, baseEnd_1266439] using wordTrace_append hprefix tailTrace_1266439
  have hstable : (prefixWord ++ tailWord_1266439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266439).length < 2 ^ (prefixWord ++ tailWord_1266439).sum := by decide
  have hdescent : baseEnd_1266439 < baseStart_1266439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266449 : List Nat := [1, 2, 2, 1, 1, 3, 4, 4, 5]
def baseStart_1266449 : Nat := 118140960795 + 1266449 * 2 ^ 59
def prefixEnd_1266449 : Nat := 4983230072969 + 3 ^ 40 * 1266449 * 2
def baseEnd_1266449 : Nat := 72255229045113416240357

theorem tailTrace_1266449 : CollatzResearch.WordTrace tailWord_1266449 prefixEnd_1266449 72255229045113416240357 := by
  unfold tailWord_1266449
  simp only [CollatzResearch.WordTrace]
  refine ⟨46191189788879040114402401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30794126525919360076268267 46191189788879040114402401)
  ·
    refine ⟨34643392341659280085801801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46191189788879040114402401 34643392341659280085801801)
    ·
      refine ⟨25982544256244460064351351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34643392341659280085801801 25982544256244460064351351)
      ·
        refine ⟨38973816384366690096527027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25982544256244460064351351 38973816384366690096527027)
        ·
          refine ⟨58460724576550035144790541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38973816384366690096527027 58460724576550035144790541)
          ·
            refine ⟨21922771716206263179296453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58460724576550035144790541 21922771716206263179296453)
            ·
              refine ⟨4110519696788674346118085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21922771716206263179296453 4110519696788674346118085)
              ·
                refine ⟨770722443147876439897141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4110519696788674346118085 770722443147876439897141)
                ·
                  refine ⟨72255229045113416240357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770722443147876439897141 72255229045113416240357)
                  ·
                    rfl

theorem cell23_1266449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 5].length) (baseStart_1266449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266449 prefixEnd_1266449 := by exact prefixLift 1266449
  have htrace : WordTrace (prefixWord ++ tailWord_1266449) baseStart_1266449 baseEnd_1266449 := by
    simpa [prefixWord, tailWord_1266449, baseEnd_1266449] using wordTrace_append hprefix tailTrace_1266449
  have hstable : (prefixWord ++ tailWord_1266449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266449).length < 2 ^ (prefixWord ++ tailWord_1266449).sum := by decide
  have hdescent : baseEnd_1266449 < baseStart_1266449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266460 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1266460 : Nat := 118140960795 + 1266460 * 2 ^ 59
def prefixEnd_1266460 : Nat := 4983230072969 + 3 ^ 40 * 1266460 * 2
def baseEnd_1266460 : Nat := 650302709693220203125663

theorem tailTrace_1266460 : CollatzResearch.WordTrace tailWord_1266460 prefixEnd_1266460 650302709693220203125663 := by
  unfold tailWord_1266460
  simp only [CollatzResearch.WordTrace]
  refine ⟨23095795495919594496526417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30794393994559459328701889 23095795495919594496526417)
  ·
    refine ⟨17321846621939695872394813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23095795495919594496526417 17321846621939695872394813)
    ·
      refine ⟨6495692483227385952148055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17321846621939695872394813 6495692483227385952148055)
      ·
        refine ⟨9743538724841078928222083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6495692483227385952148055 9743538724841078928222083)
        ·
          refine ⟨14615308087261618392333125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9743538724841078928222083 14615308087261618392333125)
          ·
            refine ⟨2740370266361553448562461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14615308087261618392333125 2740370266361553448562461)
            ·
              refine ⟨1027638849885582543210923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2740370266361553448562461 1027638849885582543210923)
              ·
                refine ⟨1541458274828373814816385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027638849885582543210923 1541458274828373814816385)
                ·
                  refine ⟨1156093706121280361112289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1541458274828373814816385 1156093706121280361112289)
                  ·
                    refine ⟨867070279590960270834217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156093706121280361112289 867070279590960270834217)
                    ·
                      refine ⟨650302709693220203125663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867070279590960270834217 650302709693220203125663)
                      ·
                        rfl

theorem cell23_1266460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1266460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266460 prefixEnd_1266460 := by exact prefixLift 1266460
  have htrace : WordTrace (prefixWord ++ tailWord_1266460) baseStart_1266460 baseEnd_1266460 := by
    simpa [prefixWord, tailWord_1266460, baseEnd_1266460] using wordTrace_append hprefix tailTrace_1266460
  have hstable : (prefixWord ++ tailWord_1266460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266460).length < 2 ^ (prefixWord ++ tailWord_1266460).sum := by decide
  have hdescent : baseEnd_1266460 < baseStart_1266460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266499 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 4]
def baseStart_1266499 : Nat := 118140960795 + 1266499 * 2 ^ 59
def prefixEnd_1266499 : Nat := 4983230072969 + 3 ^ 40 * 1266499 * 2
def baseEnd_1266499 : Nat := 650322735438745550537983

theorem tailTrace_1266499 : CollatzResearch.WordTrace tailWord_1266499 prefixEnd_1266499 650322735438745550537983 := by
  unfold tailWord_1266499
  simp only [CollatzResearch.WordTrace]
  refine ⟨46193013438697898653722551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30795342292465265769148367 46193013438697898653722551)
  ·
    refine ⟨69289520158046847980583827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46193013438697898653722551 69289520158046847980583827)
    ·
      refine ⟨103934280237070271970875741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69289520158046847980583827 103934280237070271970875741)
      ·
        refine ⟨38975355088901351989078403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103934280237070271970875741 38975355088901351989078403)
        ·
          refine ⟨58463032633352027983617605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38975355088901351989078403 58463032633352027983617605)
          ·
            refine ⟨10961818618753505246928301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58463032633352027983617605 10961818618753505246928301)
            ·
              refine ⟨4110681982032564467598113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10961818618753505246928301 4110681982032564467598113)
              ·
                refine ⟨3083011486524423350698585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110681982032564467598113 3083011486524423350698585)
                ·
                  refine ⟨2312258614893317513023939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3083011486524423350698585 2312258614893317513023939)
                  ·
                    refine ⟨3468387922339976269535909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312258614893317513023939 3468387922339976269535909)
                    ·
                      refine ⟨650322735438745550537983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3468387922339976269535909 650322735438745550537983)
                      ·
                        rfl

theorem cell23_1266499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_1266499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266499 prefixEnd_1266499 := by exact prefixLift 1266499
  have htrace : WordTrace (prefixWord ++ tailWord_1266499) baseStart_1266499 baseEnd_1266499 := by
    simpa [prefixWord, tailWord_1266499, baseEnd_1266499] using wordTrace_append hprefix tailTrace_1266499
  have hstable : (prefixWord ++ tailWord_1266499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266499).length < 2 ^ (prefixWord ++ tailWord_1266499).sum := by decide
  have hdescent : baseEnd_1266499 < baseStart_1266499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266500 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 7]
def baseStart_1266500 : Nat := 118140960795 + 1266500 * 2 ^ 59
def prefixEnd_1266500 : Nat := 4983230072969 + 3 ^ 40 * 1266500 * 2
def baseEnd_1266500 : Nat := 72258138768822227402831

theorem tailTrace_1266500 : CollatzResearch.WordTrace tailWord_1266500 prefixEnd_1266500 72258138768822227402831 := by
  unfold tailWord_1266500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23096524955847137912254477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30795366607796183883005969 23096524955847137912254477)
  ·
    refine ⟨8661196858442676717095429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23096524955847137912254477 8661196858442676717095429)
    ·
      refine ⟨1623974410958001884455393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8661196858442676717095429 1623974410958001884455393)
      ·
        refine ⟨1217980808218501413341545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623974410958001884455393 1217980808218501413341545)
        ·
          refine ⟨913485606163876060006159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217980808218501413341545 913485606163876060006159)
          ·
            refine ⟨1370228409245814090009239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913485606163876060006159 1370228409245814090009239)
            ·
              refine ⟨2055342613868721135013859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370228409245814090009239 2055342613868721135013859)
              ·
                refine ⟨3083013920803081702520789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055342613868721135013859 3083013920803081702520789)
                ·
                  refine ⟨72258138768822227402831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3083013920803081702520789 72258138768822227402831)
                  ·
                    rfl

theorem cell23_1266500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_1266500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266500 prefixEnd_1266500 := by exact prefixLift 1266500
  have htrace : WordTrace (prefixWord ++ tailWord_1266500) baseStart_1266500 baseEnd_1266500 := by
    simpa [prefixWord, tailWord_1266500, baseEnd_1266500] using wordTrace_append hprefix tailTrace_1266500
  have hstable : (prefixWord ++ tailWord_1266500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266500).length < 2 ^ (prefixWord ++ tailWord_1266500).sum := by decide
  have hdescent : baseEnd_1266500 < baseStart_1266500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266512 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_1266512 : Nat := 118140960795 + 1266512 * 2 ^ 59
def prefixEnd_1266512 : Nat := 4983230072969 + 3 ^ 40 * 1266512 * 2
def baseEnd_1266512 : Nat := 650329410687253999675423

theorem tailTrace_1266512 : CollatzResearch.WordTrace tailWord_1266512 prefixEnd_1266512 650329410687253999675423 := by
  unfold tailWord_1266512
  simp only [CollatzResearch.WordTrace]
  refine ⟨23096743793825400936972895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30795658391767201249297193 23096743793825400936972895)
  ·
    refine ⟨34645115690738101405459343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23096743793825400936972895 34645115690738101405459343)
    ·
      refine ⟨51967673536107152108189015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34645115690738101405459343 51967673536107152108189015)
      ·
        refine ⟨77951510304160728162283523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51967673536107152108189015 77951510304160728162283523)
        ·
          refine ⟨116927265456241092243425285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77951510304160728162283523 116927265456241092243425285)
          ·
            refine ⟨21923862273045204795642241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116927265456241092243425285 21923862273045204795642241)
            ·
              refine ⟨16442896704783903596731681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21923862273045204795642241 16442896704783903596731681)
              ·
                refine ⟨12332172528587927697548761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16442896704783903596731681 12332172528587927697548761)
                ·
                  refine ⟨9249129396440945773161571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12332172528587927697548761 9249129396440945773161571)
                  ·
                    refine ⟨13873694094661418659742357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9249129396440945773161571 13873694094661418659742357)
                    ·
                      refine ⟨650329410687253999675423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13873694094661418659742357 650329410687253999675423)
                      ·
                        rfl

theorem cell23_1266512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_1266512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266512 prefixEnd_1266512 := by exact prefixLift 1266512
  have htrace : WordTrace (prefixWord ++ tailWord_1266512) baseStart_1266512 baseEnd_1266512 := by
    simpa [prefixWord, tailWord_1266512, baseEnd_1266512] using wordTrace_append hprefix tailTrace_1266512
  have hstable : (prefixWord ++ tailWord_1266512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266512).length < 2 ^ (prefixWord ++ tailWord_1266512).sum := by decide
  have hdescent : baseEnd_1266512 < baseStart_1266512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266536 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1266536 : Nat := 118140960795 + 1266536 * 2 ^ 59
def prefixEnd_1266536 : Nat := 4983230072969 + 3 ^ 40 * 1266536 * 2
def baseEnd_1266536 : Nat := 650341734222961905775313

theorem tailTrace_1266536 : CollatzResearch.WordTrace tailWord_1266536 prefixEnd_1266536 650341734222961905775313 := by
  unfold tailWord_1266536
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097181469781926986409731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30796241959709235981879641 23097181469781926986409731)
  ·
    refine ⟨34645772204672890479614597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23097181469781926986409731 34645772204672890479614597)
    ·
      refine ⟨6496082288376166964927737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34645772204672890479614597 6496082288376166964927737)
      ·
        refine ⟨4872061716282125223695803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6496082288376166964927737 4872061716282125223695803)
        ·
          refine ⟨7308092574423187835543705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872061716282125223695803 7308092574423187835543705)
          ·
            refine ⟨5481069430817390876657779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7308092574423187835543705 5481069430817390876657779)
            ·
              refine ⟨8221604146226086314986669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481069430817390876657779 8221604146226086314986669)
              ·
                refine ⟨3083101554834782368120001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8221604146226086314986669 3083101554834782368120001)
                ·
                  refine ⟨2312326166126086776090001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3083101554834782368120001 2312326166126086776090001)
                  ·
                    refine ⟨1734244624594565082067501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2312326166126086776090001 1734244624594565082067501)
                    ·
                      refine ⟨650341734222961905775313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734244624594565082067501 650341734222961905775313)
                      ·
                        rfl

theorem cell23_1266536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1266536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266536 prefixEnd_1266536 := by exact prefixLift 1266536
  have htrace : WordTrace (prefixWord ++ tailWord_1266536) baseStart_1266536 baseEnd_1266536 := by
    simpa [prefixWord, tailWord_1266536, baseEnd_1266536] using wordTrace_append hprefix tailTrace_1266536
  have hstable : (prefixWord ++ tailWord_1266536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266536).length < 2 ^ (prefixWord ++ tailWord_1266536).sum := by decide
  have hdescent : baseEnd_1266536 < baseStart_1266536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266569 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_1266569 : Nat := 118140960795 + 1266569 * 2 ^ 59
def prefixEnd_1266569 : Nat := 4983230072969 + 3 ^ 40 * 1266569 * 2
def baseEnd_1266569 : Nat := 216786226361520092220887

theorem tailTrace_1266569 : CollatzResearch.WordTrace tailWord_1266569 prefixEnd_1266569 216786226361520092220887 := by
  unfold tailWord_1266569
  simp only [CollatzResearch.WordTrace]
  refine ⟨46195566548444300608770761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30797044365629533739180507 46195566548444300608770761)
  ·
    refine ⟨34646674911333225456578071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46195566548444300608770761 34646674911333225456578071)
    ·
      refine ⟨51970012366999838184867107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34646674911333225456578071 51970012366999838184867107)
      ·
        refine ⟨77955018550499757277300661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51970012366999838184867107 77955018550499757277300661)
        ·
          refine ⟨7308282989109352244746937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77955018550499757277300661 7308282989109352244746937)
          ·
            refine ⟨5481212241832014183560203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7308282989109352244746937 5481212241832014183560203)
            ·
              refine ⟨8221818362748021275340305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481212241832014183560203 8221818362748021275340305)
              ·
                refine ⟨6166363772061015956505229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8221818362748021275340305 6166363772061015956505229)
                ·
                  refine ⟨2312386414522880983689461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6166363772061015956505229 2312386414522880983689461)
                  ·
                    refine ⟨216786226361520092220887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2312386414522880983689461 216786226361520092220887)
                    ·
                      rfl

theorem cell23_1266569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_1266569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266569 prefixEnd_1266569 := by exact prefixLift 1266569
  have htrace : WordTrace (prefixWord ++ tailWord_1266569) baseStart_1266569 baseEnd_1266569 := by
    simpa [prefixWord, tailWord_1266569, baseEnd_1266569] using wordTrace_append hprefix tailTrace_1266569
  have hstable : (prefixWord ++ tailWord_1266569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266569).length < 2 ^ (prefixWord ++ tailWord_1266569).sum := by decide
  have hdescent : baseEnd_1266569 < baseStart_1266569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266593 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1266593 : Nat := 118140960795 + 1266593 * 2 ^ 59
def prefixEnd_1266593 : Nat := 4983230072969 + 3 ^ 40 * 1266593 * 2
def baseEnd_1266593 : Nat := 650371002620268182762551

theorem tailTrace_1266593 : CollatzResearch.WordTrace tailWord_1266593 prefixEnd_1266593 650371002620268182762551 := by
  unfold tailWord_1266593
  simp only [CollatzResearch.WordTrace]
  refine ⟨46196441900357352707644433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30797627933571568471762955 46196441900357352707644433)
  ·
    refine ⟨34647331425268014530733325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46196441900357352707644433 34647331425268014530733325)
    ·
      refine ⟨12992749284475505449024997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34647331425268014530733325 12992749284475505449024997)
      ·
        refine ⟨2436140490839157271692187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12992749284475505449024997 2436140490839157271692187)
        ·
          refine ⟨3654210736258735907538281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436140490839157271692187 3654210736258735907538281)
          ·
            refine ⟨2740658052194051930653711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3654210736258735907538281 2740658052194051930653711)
            ·
              refine ⟨4110987078291077895980567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740658052194051930653711 4110987078291077895980567)
              ·
                refine ⟨6166480617436616843970851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4110987078291077895980567 6166480617436616843970851)
                ·
                  refine ⟨9249720926154925265956277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6166480617436616843970851 9249720926154925265956277)
                  ·
                    refine ⟨867161336827024243683401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9249720926154925265956277 867161336827024243683401)
                    ·
                      refine ⟨650371002620268182762551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867161336827024243683401 650371002620268182762551)
                      ·
                        rfl

theorem cell23_1266593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1266593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266593 prefixEnd_1266593 := by exact prefixLift 1266593
  have htrace : WordTrace (prefixWord ++ tailWord_1266593) baseStart_1266593 baseEnd_1266593 := by
    simpa [prefixWord, tailWord_1266593, baseEnd_1266593] using wordTrace_append hprefix tailTrace_1266593
  have hstable : (prefixWord ++ tailWord_1266593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266593).length < 2 ^ (prefixWord ++ tailWord_1266593).sum := by decide
  have hdescent : baseEnd_1266593 < baseStart_1266593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266616 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 4, 4]
def baseStart_1266616 : Nat := 118140960795 + 1266616 * 2 ^ 59
def prefixEnd_1266616 : Nat := 4983230072969 + 3 ^ 40 * 1266616 * 2
def baseEnd_1266616 : Nat := 216794270891773864258315

theorem tailTrace_1266616 : CollatzResearch.WordTrace tailWord_1266616 prefixEnd_1266616 216794270891773864258315 := by
  unfold tailWord_1266616
  simp only [CollatzResearch.WordTrace]
  refine ⟨23098640389637013817865851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30798187186182685090487801 23098640389637013817865851)
  ·
    refine ⟨34647960584455520726798777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23098640389637013817865851 34647960584455520726798777)
    ·
      refine ⟨25985970438341640545099083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34647960584455520726798777 25985970438341640545099083)
      ·
        refine ⟨38978955657512460817648625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25985970438341640545099083 38978955657512460817648625)
        ·
          refine ⟨29234216743134345613236469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38978955657512460817648625 29234216743134345613236469)
          ·
            refine ⟨2740707819668844901240919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29234216743134345613236469 2740707819668844901240919)
            ·
              refine ⟨4111061729503267351861379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740707819668844901240919 4111061729503267351861379)
              ·
                refine ⟨6166592594254901027792069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111061729503267351861379 6166592594254901027792069)
                ·
                  refine ⟨1156236111422793942711013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6166592594254901027792069 1156236111422793942711013)
                  ·
                    refine ⟨216794270891773864258315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1156236111422793942711013 216794270891773864258315)
                    ·
                      rfl

theorem cell23_1266616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_1266616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266616 prefixEnd_1266616 := by exact prefixLift 1266616
  have htrace : WordTrace (prefixWord ++ tailWord_1266616) baseStart_1266616 baseEnd_1266616 := by
    simpa [prefixWord, tailWord_1266616, baseEnd_1266616] using wordTrace_append hprefix tailTrace_1266616
  have hstable : (prefixWord ++ tailWord_1266616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266616).length < 2 ^ (prefixWord ++ tailWord_1266616).sum := by decide
  have hdescent : baseEnd_1266616 < baseStart_1266616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266673 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_1266673 : Nat := 118140960795 + 1266673 * 2 ^ 59
def prefixEnd_1266673 : Nat := 4983230072969 + 3 ^ 40 * 1266673 * 2
def baseEnd_1266673 : Nat := 650412081072627869762183

theorem tailTrace_1266673 : CollatzResearch.WordTrace tailWord_1266673 prefixEnd_1266673 650412081072627869762183 := by
  unfold tailWord_1266673
  simp only [CollatzResearch.WordTrace]
  refine ⟨46199359740067526370556673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30799573160045017580371115 46199359740067526370556673)
  ·
    refine ⟨34649519805050644777917505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46199359740067526370556673 34649519805050644777917505)
    ·
      refine ⟨25987139853787983583438129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34649519805050644777917505 25987139853787983583438129)
      ·
        refine ⟨19490354890340987687578597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25987139853787983583438129 19490354890340987687578597)
        ·
          refine ⟨3654441541938935191420987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19490354890340987687578597 3654441541938935191420987)
          ·
            refine ⟨5481662312908402787131481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654441541938935191420987 5481662312908402787131481)
            ·
              refine ⟨4111246734681302090348611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5481662312908402787131481 4111246734681302090348611)
              ·
                refine ⟨6166870102021953135522917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111246734681302090348611 6166870102021953135522917)
                ·
                  refine ⟨1156288144129116212910547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6166870102021953135522917 1156288144129116212910547)
                  ·
                    refine ⟨1734432216193674319365821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1156288144129116212910547 1734432216193674319365821)
                    ·
                      refine ⟨650412081072627869762183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734432216193674319365821 650412081072627869762183)
                      ·
                        rfl

theorem cell23_1266673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_1266673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266673 prefixEnd_1266673 := by exact prefixLift 1266673
  have htrace : WordTrace (prefixWord ++ tailWord_1266673) baseStart_1266673 baseEnd_1266673 := by
    simpa [prefixWord, tailWord_1266673, baseEnd_1266673] using wordTrace_append hprefix tailTrace_1266673
  have hstable : (prefixWord ++ tailWord_1266673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266673).length < 2 ^ (prefixWord ++ tailWord_1266673).sum := by decide
  have hdescent : baseEnd_1266673 < baseStart_1266673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266674 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1266674 : Nat := 118140960795 + 1266674 * 2 ^ 59
def prefixEnd_1266674 : Nat := 4983230072969 + 3 ^ 40 * 1266674 * 2
def baseEnd_1266674 : Nat := 650412594553282365849679

theorem tailTrace_1266674 : CollatzResearch.WordTrace tailWord_1266674 prefixEnd_1266674 650412594553282365849679 := by
  unfold tailWord_1266674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11549849053265975885335769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30799597475375935694228717 11549849053265975885335769)
  ·
    refine ⟨8662386789949481914001827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11549849053265975885335769 8662386789949481914001827)
    ·
      refine ⟨12993580184924222871002741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8662386789949481914001827 12993580184924222871002741)
      ·
        refine ⟨1218148142336645894156507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12993580184924222871002741 1218148142336645894156507)
        ·
          refine ⟨1827222213504968841234761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218148142336645894156507 1827222213504968841234761)
          ·
            refine ⟨1370416660128726630926071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827222213504968841234761 1370416660128726630926071)
            ·
              refine ⟨2055624990193089946389107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370416660128726630926071 2055624990193089946389107)
              ·
                refine ⟨3083437485289634919583661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055624990193089946389107 3083437485289634919583661)
                ·
                  refine ⟨1156289056983613094843873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3083437485289634919583661 1156289056983613094843873)
                  ·
                    refine ⟨867216792737709821132905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156289056983613094843873 867216792737709821132905)
                    ·
                      refine ⟨650412594553282365849679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867216792737709821132905 650412594553282365849679)
                      ·
                        rfl

theorem cell23_1266674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1266674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266674 prefixEnd_1266674 := by exact prefixLift 1266674
  have htrace : WordTrace (prefixWord ++ tailWord_1266674) baseStart_1266674 baseEnd_1266674 := by
    simpa [prefixWord, tailWord_1266674, baseEnd_1266674] using wordTrace_append hprefix tailTrace_1266674
  have hstable : (prefixWord ++ tailWord_1266674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266674).length < 2 ^ (prefixWord ++ tailWord_1266674).sum := by decide
  have hdescent : baseEnd_1266674 < baseStart_1266674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266700 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 1, 3, 2]
def baseStart_1266700 : Nat := 118140960795 + 1266700 * 2 ^ 59
def prefixEnd_1266700 : Nat := 4983230072969 + 3 ^ 40 * 1266700 * 2
def baseEnd_1266700 : Nat := 650425945050299264124559

theorem tailTrace_1266700 : CollatzResearch.WordTrace tailWord_1266700 prefixEnd_1266700 650425945050299264124559 := by
  unfold tailWord_1266700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23100172255484854990894777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30800229673979806654526369 23100172255484854990894777)
  ·
    refine ⟨17325129191613641243171083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23100172255484854990894777 17325129191613641243171083)
    ·
      refine ⟨25987693787420461864756625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17325129191613641243171083 25987693787420461864756625)
      ·
        refine ⟨19490770340565346398567469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25987693787420461864756625 19490770340565346398567469)
        ·
          refine ⟨7309038877712004899462801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19490770340565346398567469 7309038877712004899462801)
          ·
            refine ⟨5481779158284003674597101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309038877712004899462801 5481779158284003674597101)
            ·
              refine ⟨2055667184356501377973913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5481779158284003674597101 2055667184356501377973913)
              ·
                refine ⟨1541750388267376033480435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055667184356501377973913 1541750388267376033480435)
                ·
                  refine ⟨2312625582401064050220653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541750388267376033480435 2312625582401064050220653)
                  ·
                    refine ⟨867234593400399018832745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312625582401064050220653 867234593400399018832745)
                    ·
                      refine ⟨650425945050299264124559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867234593400399018832745 650425945050299264124559)
                      ·
                        rfl

theorem cell23_1266700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_1266700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266700 prefixEnd_1266700 := by exact prefixLift 1266700
  have htrace : WordTrace (prefixWord ++ tailWord_1266700) baseStart_1266700 baseEnd_1266700 := by
    simpa [prefixWord, tailWord_1266700, baseEnd_1266700] using wordTrace_append hprefix tailTrace_1266700
  have hstable : (prefixWord ++ tailWord_1266700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266700).length < 2 ^ (prefixWord ++ tailWord_1266700).sum := by decide
  have hdescent : baseEnd_1266700 < baseStart_1266700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266713 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 6, 2, 2]
def baseStart_1266713 : Nat := 118140960795 + 1266713 * 2 ^ 59
def prefixEnd_1266713 : Nat := 4983230072969 + 3 ^ 40 * 1266713 * 2
def baseEnd_1266713 : Nat := 650432620298807713261999

theorem tailTrace_1266713 : CollatzResearch.WordTrace tailWord_1266713 prefixEnd_1266713 650432620298807713261999 := by
  unfold tailWord_1266713
  simp only [CollatzResearch.WordTrace]
  refine ⟨46200818659922613202012793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30800545773281742134675195 46200818659922613202012793)
  ·
    refine ⟨34650613994941959901509595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46200818659922613202012793 34650613994941959901509595)
    ·
      refine ⟨51975920992412939852264393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34650613994941959901509595 51975920992412939852264393)
      ·
        refine ⟨38981940744309704889198295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51975920992412939852264393 38981940744309704889198295)
        ·
          refine ⟨58472911116464557333797443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38981940744309704889198295 58472911116464557333797443)
          ·
            refine ⟨87709366674696836000696165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58472911116464557333797443 87709366674696836000696165)
            ·
              refine ⟨16445506251505656750130531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87709366674696836000696165 16445506251505656750130531)
              ·
                refine ⟨24668259377258485125195797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16445506251505656750130531 24668259377258485125195797)
                ·
                  refine ⟨1156324658308991490243553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24668259377258485125195797 1156324658308991490243553)
                  ·
                    refine ⟨867243493731743617682665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156324658308991490243553 867243493731743617682665)
                    ·
                      refine ⟨650432620298807713261999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867243493731743617682665 650432620298807713261999)
                      ·
                        rfl

theorem cell23_1266713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_1266713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266713 prefixEnd_1266713 := by exact prefixLift 1266713
  have htrace : WordTrace (prefixWord ++ tailWord_1266713) baseStart_1266713 baseEnd_1266713 := by
    simpa [prefixWord, tailWord_1266713, baseEnd_1266713] using wordTrace_append hprefix tailTrace_1266713
  have hstable : (prefixWord ++ tailWord_1266713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266713).length < 2 ^ (prefixWord ++ tailWord_1266713).sum := by decide
  have hdescent : baseEnd_1266713 < baseStart_1266713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266739 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_1266739 : Nat := 118140960795 + 1266739 * 2 ^ 59
def prefixEnd_1266739 : Nat := 4983230072969 + 3 ^ 40 * 1266739 * 2
def baseEnd_1266739 : Nat := 650445970795824611536879

theorem tailTrace_1266739 : CollatzResearch.WordTrace tailWord_1266739 prefixEnd_1266739 650445970795824611536879 := by
  unfold tailWord_1266739
  simp only [CollatzResearch.WordTrace]
  refine ⟨46201766957828419642459271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30801177971885613094972847 46201766957828419642459271)
  ·
    refine ⟨69302650436742629463688907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46201766957828419642459271 69302650436742629463688907)
    ·
      refine ⟨103953975655113944195533361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69302650436742629463688907 103953975655113944195533361)
      ·
        refine ⟨77965481741335458146650021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103953975655113944195533361 77965481741335458146650021)
        ·
          refine ⟨14618527826500398402496879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77965481741335458146650021 14618527826500398402496879)
          ·
            refine ⟨21927791739750597603745319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14618527826500398402496879 21927791739750597603745319)
            ·
              refine ⟨32891687609625896405617979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21927791739750597603745319 32891687609625896405617979)
              ·
                refine ⟨49337531414438844608426969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32891687609625896405617979 49337531414438844608426969)
                ·
                  refine ⟨37003148560829133456320227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49337531414438844608426969 37003148560829133456320227)
                  ·
                    refine ⟨55504722841243700184480341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37003148560829133456320227 55504722841243700184480341)
                    ·
                      refine ⟨650445970795824611536879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 55504722841243700184480341 650445970795824611536879)
                      ·
                        rfl

theorem cell23_1266739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_1266739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266739 prefixEnd_1266739 := by exact prefixLift 1266739
  have htrace : WordTrace (prefixWord ++ tailWord_1266739) baseStart_1266739 baseEnd_1266739 := by
    simpa [prefixWord, tailWord_1266739, baseEnd_1266739] using wordTrace_append hprefix tailTrace_1266739
  have hstable : (prefixWord ++ tailWord_1266739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266739).length < 2 ^ (prefixWord ++ tailWord_1266739).sum := by decide
  have hdescent : baseEnd_1266739 < baseStart_1266739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266746 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_1266746 : Nat := 118140960795 + 1266746 * 2 ^ 59
def prefixEnd_1266746 : Nat := 4983230072969 + 3 ^ 40 * 1266746 * 2
def baseEnd_1266746 : Nat := 650449565160406084149347

theorem tailTrace_1266746 : CollatzResearch.WordTrace tailWord_1266746 prefixEnd_1266746 650449565160406084149347 := by
  unfold tailWord_1266746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550505567200764959491023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30801348179202039891976061 11550505567200764959491023)
  ·
    refine ⟨17325758350801147439236535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11550505567200764959491023 17325758350801147439236535)
    ·
      refine ⟨25988637526201721158854803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17325758350801147439236535 25988637526201721158854803)
      ·
        refine ⟨38982956289302581738282205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25988637526201721158854803 38982956289302581738282205)
        ·
          refine ⟨14618608608488468151855827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38982956289302581738282205 14618608608488468151855827)
          ·
            refine ⟨21927912912732702227783741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14618608608488468151855827 21927912912732702227783741)
            ·
              refine ⟨8222967342274763335418903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21927912912732702227783741 8222967342274763335418903)
              ·
                refine ⟨12334451013412145003128355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222967342274763335418903 12334451013412145003128355)
                ·
                  refine ⟨18501676520118217504692533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12334451013412145003128355 18501676520118217504692533)
                  ·
                    refine ⟨1734532173761082891064925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18501676520118217504692533 1734532173761082891064925)
                    ·
                      refine ⟨650449565160406084149347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734532173761082891064925 650449565160406084149347)
                      ·
                        rfl

theorem cell23_1266746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_1266746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266746 prefixEnd_1266746 := by exact prefixLift 1266746
  have htrace : WordTrace (prefixWord ++ tailWord_1266746) baseStart_1266746 baseEnd_1266746 := by
    simpa [prefixWord, tailWord_1266746, baseEnd_1266746] using wordTrace_append hprefix tailTrace_1266746
  have hstable : (prefixWord ++ tailWord_1266746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266746).length < 2 ^ (prefixWord ++ tailWord_1266746).sum := by decide
  have hdescent : baseEnd_1266746 < baseStart_1266746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266753 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 7]
def baseStart_1266753 : Nat := 118140960795 + 1266753 * 2 ^ 59
def prefixEnd_1266753 : Nat := 4983230072969 + 3 ^ 40 * 1266753 * 2
def baseEnd_1266753 : Nat := 72272573280554172973535

theorem tailTrace_1266753 : CollatzResearch.WordTrace tailWord_1266753 prefixEnd_1266753 72272573280554172973535 := by
  unfold tailWord_1266753
  simp only [CollatzResearch.WordTrace]
  refine ⟨46202277579777700033468913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30801518386518466688979275 46202277579777700033468913)
  ·
    refine ⟨34651708184833275025101685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46202277579777700033468913 34651708184833275025101685)
    ·
      refine ⟨3248597642328119533603283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34651708184833275025101685 3248597642328119533603283)
      ·
        refine ⟨4872896463492179300404925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248597642328119533603283 4872896463492179300404925)
        ·
          refine ⟨1827336173809567237651847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4872896463492179300404925 1827336173809567237651847)
          ·
            refine ⟨2741004260714350856477771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827336173809567237651847 2741004260714350856477771)
            ·
              refine ⟨4111506391071526284716657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741004260714350856477771 4111506391071526284716657)
              ·
                refine ⟨3083629793303644713537493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4111506391071526284716657 3083629793303644713537493)
                ·
                  refine ⟨72272573280554172973535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3083629793303644713537493 72272573280554172973535)
                  ·
                    rfl

theorem cell23_1266753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 7].length) (baseStart_1266753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266753 prefixEnd_1266753 := by exact prefixLift 1266753
  have htrace : WordTrace (prefixWord ++ tailWord_1266753) baseStart_1266753 baseEnd_1266753 := by
    simpa [prefixWord, tailWord_1266753, baseEnd_1266753] using wordTrace_append hprefix tailTrace_1266753
  have hstable : (prefixWord ++ tailWord_1266753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266753).length < 2 ^ (prefixWord ++ tailWord_1266753).sum := by decide
  have hdescent : baseEnd_1266753 < baseStart_1266753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266766 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1266766 : Nat := 118140960795 + 1266766 * 2 ^ 59
def prefixEnd_1266766 : Nat := 4983230072969 + 3 ^ 40 * 1266766 * 2
def baseEnd_1266766 : Nat := 216819944924498668633085

theorem tailTrace_1266766 : CollatzResearch.WordTrace tailWord_1266766 prefixEnd_1266766 216819944924498668633085 := by
  unfold tailWord_1266766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775343966091325406711519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30801834485820402169128101 5775343966091325406711519)
  ·
    refine ⟨8663015949136988110067279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5775343966091325406711519 8663015949136988110067279)
    ·
      refine ⟨12994523923705482165100919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8663015949136988110067279 12994523923705482165100919)
      ·
        refine ⟨19491785885558223247651379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12994523923705482165100919 19491785885558223247651379)
        ·
          refine ⟨29237678828337334871477069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19491785885558223247651379 29237678828337334871477069)
          ·
            refine ⟨10964129560626500576803901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29237678828337334871477069 10964129560626500576803901)
            ·
              refine ⟨4111548585234937716301463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10964129560626500576803901 4111548585234937716301463)
              ·
                refine ⟨6167322877852406574452195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111548585234937716301463 6167322877852406574452195)
                ·
                  refine ⟨9250984316778609861678293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6167322877852406574452195 9250984316778609861678293)
                  ·
                    refine ⟨216819944924498668633085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9250984316778609861678293 216819944924498668633085)
                    ·
                      rfl

theorem cell23_1266766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1266766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266766 prefixEnd_1266766 := by exact prefixLift 1266766
  have htrace : WordTrace (prefixWord ++ tailWord_1266766) baseStart_1266766 baseEnd_1266766 := by
    simpa [prefixWord, tailWord_1266766, baseEnd_1266766] using wordTrace_append hprefix tailTrace_1266766
  have hstable : (prefixWord ++ tailWord_1266766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266766).length < 2 ^ (prefixWord ++ tailWord_1266766).sum := by decide
  have hdescent : baseEnd_1266766 < baseStart_1266766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266770 : List Nat := [3, 2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_1266770 : Nat := 118140960795 + 1266770 * 2 ^ 59
def prefixEnd_1266770 : Nat := 4983230072969 + 3 ^ 40 * 1266770 * 2
def baseEnd_1266770 : Nat := 72273543188457110027693

theorem tailTrace_1266770 : CollatzResearch.WordTrace tailWord_1266770 prefixEnd_1266770 72273543188457110027693 := by
  unfold tailWord_1266770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550724405179027984209441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30801931747144074624558509 11550724405179027984209441)
  ·
    refine ⟨8663043303884270988157081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11550724405179027984209441 8663043303884270988157081)
    ·
      refine ⟨6497282477913203241117811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8663043303884270988157081 6497282477913203241117811)
      ·
        refine ⟨9745923716869804861676717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6497282477913203241117811 9745923716869804861676717)
        ·
          refine ⟨3654721393826176823128769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9745923716869804861676717 3654721393826176823128769)
          ·
            refine ⟨2741041045369632617346577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3654721393826176823128769 2741041045369632617346577)
            ·
              refine ⟨2055780784027224463009933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2741041045369632617346577 2055780784027224463009933)
              ·
                refine ⟨770917794010209173628725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2055780784027224463009933 770917794010209173628725)
                ·
                  refine ⟨72273543188457110027693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 770917794010209173628725 72273543188457110027693)
                  ·
                    rfl

theorem cell23_1266770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_1266770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266770 prefixEnd_1266770 := by exact prefixLift 1266770
  have htrace : WordTrace (prefixWord ++ tailWord_1266770) baseStart_1266770 baseEnd_1266770 := by
    simpa [prefixWord, tailWord_1266770, baseEnd_1266770] using wordTrace_append hprefix tailTrace_1266770
  have hstable : (prefixWord ++ tailWord_1266770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266770).length < 2 ^ (prefixWord ++ tailWord_1266770).sum := by decide
  have hdescent : baseEnd_1266770 < baseStart_1266770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266781 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1266781 : Nat := 118140960795 + 1266781 * 2 ^ 59
def prefixEnd_1266781 : Nat := 4983230072969 + 3 ^ 40 * 1266781 * 2
def baseEnd_1266781 : Nat := 650467536983313447211687

theorem tailTrace_1266781 : CollatzResearch.WordTrace tailWord_1266781 prefixEnd_1266781 650467536983313447211687 := by
  unfold tailWord_1266781
  simp only [CollatzResearch.WordTrace]
  refine ⟨46203298823676260815488197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30802199215784173876992131 46203298823676260815488197)
  ·
    refine ⟨8663118529439298902904037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46203298823676260815488197 8663118529439298902904037)
    ·
      refine ⟨1624334724269868544294507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8663118529439298902904037 1624334724269868544294507)
      ·
        refine ⟨2436502086404802816441761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624334724269868544294507 2436502086404802816441761)
        ·
          refine ⟨1827376564803602112331321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436502086404802816441761 1827376564803602112331321)
          ·
            refine ⟨1370532423602701584248491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827376564803602112331321 1370532423602701584248491)
            ·
              refine ⟨2055798635404052376372737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370532423602701584248491 2055798635404052376372737)
              ·
                refine ⟨1541848976553039282279553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055798635404052376372737 1541848976553039282279553)
                ·
                  refine ⟨1156386732414779461709665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1541848976553039282279553 1156386732414779461709665)
                  ·
                    refine ⟨867290049311084596282249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156386732414779461709665 867290049311084596282249)
                    ·
                      refine ⟨650467536983313447211687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867290049311084596282249 650467536983313447211687)
                      ·
                        rfl

theorem cell23_1266781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1266781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266781 prefixEnd_1266781 := by exact prefixLift 1266781
  have htrace : WordTrace (prefixWord ++ tailWord_1266781) baseStart_1266781 baseEnd_1266781 := by
    simpa [prefixWord, tailWord_1266781, baseEnd_1266781] using wordTrace_append hprefix tailTrace_1266781
  have hstable : (prefixWord ++ tailWord_1266781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266781).length < 2 ^ (prefixWord ++ tailWord_1266781).sum := by decide
  have hdescent : baseEnd_1266781 < baseStart_1266781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266813 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1266813 : Nat := 118140960795 + 1266813 * 2 ^ 59
def prefixEnd_1266813 : Nat := 4983230072969 + 3 ^ 40 * 1266813 * 2
def baseEnd_1266813 : Nat := 216827989454752440670513

theorem tailTrace_1266813 : CollatzResearch.WordTrace tailWord_1266813 prefixEnd_1266813 216827989454752440670513 := by
  unfold tailWord_1266813
  simp only [CollatzResearch.WordTrace]
  refine ⟨46204465959560330280653093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30802977306373553520435395 46204465959560330280653093)
  ·
    refine ⟨8663337367417561927622455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46204465959560330280653093 8663337367417561927622455)
    ·
      refine ⟨12995006051126342891433683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8663337367417561927622455 12995006051126342891433683)
      ·
        refine ⟨19492509076689514337150525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12995006051126342891433683 19492509076689514337150525)
        ·
          refine ⟨7309690903758567876431447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19492509076689514337150525 7309690903758567876431447)
          ·
            refine ⟨10964536355637851814647171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7309690903758567876431447 10964536355637851814647171)
            ·
              refine ⟨16446804533456777721970757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10964536355637851814647171 16446804533456777721970757)
              ·
                refine ⟨3083775850023145822869517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16446804533456777721970757 3083775850023145822869517)
                ·
                  refine ⟨1156415943758679683576069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3083775850023145822869517 1156415943758679683576069)
                  ·
                    refine ⟨216827989454752440670513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1156415943758679683576069 216827989454752440670513)
                    ·
                      rfl

theorem cell23_1266813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1266813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266813 prefixEnd_1266813 := by exact prefixLift 1266813
  have htrace : WordTrace (prefixWord ++ tailWord_1266813) baseStart_1266813 baseEnd_1266813 := by
    simpa [prefixWord, tailWord_1266813, baseEnd_1266813] using wordTrace_append hprefix tailTrace_1266813
  have hstable : (prefixWord ++ tailWord_1266813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266813).length < 2 ^ (prefixWord ++ tailWord_1266813).sum := by decide
  have hdescent : baseEnd_1266813 < baseStart_1266813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266823 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1266823 : Nat := 118140960795 + 1266823 * 2 ^ 59
def prefixEnd_1266823 : Nat := 4983230072969 + 3 ^ 40 * 1266823 * 2
def baseEnd_1266823 : Nat := 650489103170802282886493

theorem tailTrace_1266823 : CollatzResearch.WordTrace tailWord_1266823 prefixEnd_1266823 650489103170802282886493 := by
  unfold tailWord_1266823
  simp only [CollatzResearch.WordTrace]
  refine ⟨46204830689524101988517123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30803220459682734659011415 46204830689524101988517123)
  ·
    refine ⟨69307246034286152982775685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46204830689524101988517123 69307246034286152982775685)
    ·
      refine ⟨12995108631428653684270441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69307246034286152982775685 12995108631428653684270441)
      ·
        refine ⟨9746331473571490263202831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12995108631428653684270441 9746331473571490263202831)
        ·
          refine ⟨14619497210357235394804247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9746331473571490263202831 14619497210357235394804247)
          ·
            refine ⟨21929245815535853092206371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14619497210357235394804247 21929245815535853092206371)
            ·
              refine ⟨32893868723303779638309557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21929245815535853092206371 32893868723303779638309557)
              ·
                refine ⟨3083800192809729341091521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32893868723303779638309557 3083800192809729341091521)
                ·
                  refine ⟨2312850144607297005818641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3083800192809729341091521 2312850144607297005818641)
                  ·
                    refine ⟨1734637608455472754363981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2312850144607297005818641 1734637608455472754363981)
                    ·
                      refine ⟨650489103170802282886493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734637608455472754363981 650489103170802282886493)
                      ·
                        rfl

theorem cell23_1266823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1266823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266823 prefixEnd_1266823 := by exact prefixLift 1266823
  have htrace : WordTrace (prefixWord ++ tailWord_1266823) baseStart_1266823 baseEnd_1266823 := by
    simpa [prefixWord, tailWord_1266823, baseEnd_1266823] using wordTrace_append hprefix tailTrace_1266823
  have hstable : (prefixWord ++ tailWord_1266823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266823).length < 2 ^ (prefixWord ++ tailWord_1266823).sum := by decide
  have hdescent : baseEnd_1266823 < baseStart_1266823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266826 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_1266826 : Nat := 118140960795 + 1266826 * 2 ^ 59
def prefixEnd_1266826 : Nat := 4983230072969 + 3 ^ 40 * 1266826 * 2
def baseEnd_1266826 : Nat := 72276738179196196794331

theorem tailTrace_1266826 : CollatzResearch.WordTrace tailWord_1266826 prefixEnd_1266826 72276738179196196794331 := by
  unfold tailWord_1266826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11551235027128308375219083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30803293405675489000584221 11551235027128308375219083)
  ·
    refine ⟨17326852540692462562828625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11551235027128308375219083 17326852540692462562828625)
    ·
      refine ⟨12995139405519346922121469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17326852540692462562828625 12995139405519346922121469)
      ·
        refine ⟨4873177277069755095795551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12995139405519346922121469 4873177277069755095795551)
        ·
          refine ⟨7309765915604632643693327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873177277069755095795551 7309765915604632643693327)
          ·
            refine ⟨10964648873406948965539991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7309765915604632643693327 10964648873406948965539991)
            ·
              refine ⟨16446973310110423448309987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10964648873406948965539991 16446973310110423448309987)
              ·
                refine ⟨24670459965165635172464981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16446973310110423448309987 24670459965165635172464981)
                ·
                  refine ⟨72276738179196196794331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24670459965165635172464981 72276738179196196794331)
                  ·
                    rfl

theorem cell23_1266826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_1266826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266826 prefixEnd_1266826 := by exact prefixLift 1266826
  have htrace : WordTrace (prefixWord ++ tailWord_1266826) baseStart_1266826 baseEnd_1266826 := by
    simpa [prefixWord, tailWord_1266826, baseEnd_1266826] using wordTrace_append hprefix tailTrace_1266826
  have hstable : (prefixWord ++ tailWord_1266826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266826).length < 2 ^ (prefixWord ++ tailWord_1266826).sum := by decide
  have hdescent : baseEnd_1266826 < baseStart_1266826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266840 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1266840 : Nat := 118140960795 + 1266840 * 2 ^ 59
def prefixEnd_1266840 : Nat := 4983230072969 + 3 ^ 40 * 1266840 * 2
def baseEnd_1266840 : Nat := 650497832341928716373915

theorem tailTrace_1266840 : CollatzResearch.WordTrace tailWord_1266840 prefixEnd_1266840 650497832341928716373915 := by
  unfold tailWord_1266840
  simp only [CollatzResearch.WordTrace]
  refine ⟨23102725365231256945942987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30803633820308342594590649 23102725365231256945942987)
  ·
    refine ⟨34654088047846885418914481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23102725365231256945942987 34654088047846885418914481)
    ·
      refine ⟨25990566035885164064185861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34654088047846885418914481 25990566035885164064185861)
      ·
        refine ⟨4873231131728468262034849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25990566035885164064185861 4873231131728468262034849)
        ·
          refine ⟨3654923348796351196526137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4873231131728468262034849 3654923348796351196526137)
          ·
            refine ⟨2741192511597263397394603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3654923348796351196526137 2741192511597263397394603)
            ·
              refine ⟨4111788767395895096091905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741192511597263397394603 4111788767395895096091905)
              ·
                refine ⟨3083841575546921322068929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4111788767395895096091905 3083841575546921322068929)
                ·
                  refine ⟨2312881181660190991551697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3083841575546921322068929 2312881181660190991551697)
                  ·
                    refine ⟨1734660886245143243663773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2312881181660190991551697 1734660886245143243663773)
                    ·
                      refine ⟨650497832341928716373915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734660886245143243663773 650497832341928716373915)
                      ·
                        rfl

theorem cell23_1266840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1266840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266840 prefixEnd_1266840 := by exact prefixLift 1266840
  have htrace : WordTrace (prefixWord ++ tailWord_1266840) baseStart_1266840 baseEnd_1266840 := by
    simpa [prefixWord, tailWord_1266840, baseEnd_1266840] using wordTrace_append hprefix tailTrace_1266840
  have hstable : (prefixWord ++ tailWord_1266840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266840).length < 2 ^ (prefixWord ++ tailWord_1266840).sum := by decide
  have hdescent : baseEnd_1266840 < baseStart_1266840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266847 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 3, 4]
def baseStart_1266847 : Nat := 118140960795 + 1266847 * 2 ^ 59
def prefixEnd_1266847 : Nat := 4983230072969 + 3 ^ 40 * 1266847 * 2
def baseEnd_1266847 : Nat := 216833808902170062995461

theorem tailTrace_1266847 : CollatzResearch.WordTrace tailWord_1266847 prefixEnd_1266847 216833808902170062995461 := by
  unfold tailWord_1266847
  simp only [CollatzResearch.WordTrace]
  refine ⟨46205706041437154087390795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30803804027624769391593863 46205706041437154087390795)
  ·
    refine ⟨69308559062155731131086193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46205706041437154087390795 69308559062155731131086193)
    ·
      refine ⟨51981419296616798348314645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69308559062155731131086193 51981419296616798348314645)
      ·
        refine ⟨2436629029528912422577249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51981419296616798348314645 2436629029528912422577249)
        ·
          refine ⟨1827471772146684316932937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436629029528912422577249 1827471772146684316932937)
          ·
            refine ⟨1370603829110013237699703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827471772146684316932937 1370603829110013237699703)
            ·
              refine ⟨2055905743665019856549555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370603829110013237699703 2055905743665019856549555)
              ·
                refine ⟨3083858615497529784824333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055905743665019856549555 3083858615497529784824333)
                ·
                  refine ⟨1156446980811573669309125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3083858615497529784824333 1156446980811573669309125)
                  ·
                    refine ⟨216833808902170062995461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1156446980811573669309125 216833808902170062995461)
                    ·
                      rfl

theorem cell23_1266847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_1266847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266847 prefixEnd_1266847 := by exact prefixLift 1266847
  have htrace : WordTrace (prefixWord ++ tailWord_1266847) baseStart_1266847 baseEnd_1266847 := by
    simpa [prefixWord, tailWord_1266847, baseEnd_1266847] using wordTrace_append hprefix tailTrace_1266847
  have hstable : (prefixWord ++ tailWord_1266847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266847).length < 2 ^ (prefixWord ++ tailWord_1266847).sum := by decide
  have hdescent : baseEnd_1266847 < baseStart_1266847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266863 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 3, 5, 2]
def baseStart_1266863 : Nat := 118140960795 + 1266863 * 2 ^ 59
def prefixEnd_1266863 : Nat := 4983230072969 + 3 ^ 40 * 1266863 * 2
def baseEnd_1266863 : Nat := 650509642396982126386309

theorem tailTrace_1266863 : CollatzResearch.WordTrace tailWord_1266863 prefixEnd_1266863 650509642396982126386309 := by
  unfold tailWord_1266863
  simp only [CollatzResearch.WordTrace]
  refine ⟨46206289609379188819973243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30804193072919459213315495 46206289609379188819973243)
  ·
    refine ⟨69309434414068783229959865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46206289609379188819973243 69309434414068783229959865)
    ·
      refine ⟨51982075810551587422469899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69309434414068783229959865 51982075810551587422469899)
      ·
        refine ⟨77973113715827381133704849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51982075810551587422469899 77973113715827381133704849)
        ·
          refine ⟨58479835286870535850278637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77973113715827381133704849 58479835286870535850278637)
          ·
            refine ⟨21929938232576450943854489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58479835286870535850278637 21929938232576450943854489)
            ·
              refine ⟨16447453674432338207890867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21929938232576450943854489 16447453674432338207890867)
              ·
                refine ⟨24671180511648507311836301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16447453674432338207890867 24671180511648507311836301)
                ·
                  refine ⟨9251692691868190241938613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24671180511648507311836301 9251692691868190241938613)
                  ·
                    refine ⟨867346189862642835181745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9251692691868190241938613 867346189862642835181745)
                    ·
                      refine ⟨650509642396982126386309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867346189862642835181745 650509642396982126386309)
                      ·
                        rfl

theorem cell23_1266863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5, 2].length) (baseStart_1266863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266863 prefixEnd_1266863 := by exact prefixLift 1266863
  have htrace : WordTrace (prefixWord ++ tailWord_1266863) baseStart_1266863 baseEnd_1266863 := by
    simpa [prefixWord, tailWord_1266863, baseEnd_1266863] using wordTrace_append hprefix tailTrace_1266863
  have hstable : (prefixWord ++ tailWord_1266863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266863).length < 2 ^ (prefixWord ++ tailWord_1266863).sum := by decide
  have hdescent : baseEnd_1266863 < baseStart_1266863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266873 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 3, 5]
def baseStart_1266873 : Nat := 118140960795 + 1266873 * 2 ^ 59
def prefixEnd_1266873 : Nat := 4983230072969 + 3 ^ 40 * 1266873 * 2
def baseEnd_1266873 : Nat := 216838259067842362420421

theorem tailTrace_1266873 : CollatzResearch.WordTrace tailWord_1266873 prefixEnd_1266873 216838259067842362420421 := by
  unfold tailWord_1266873
  simp only [CollatzResearch.WordTrace]
  refine ⟨46206654339342960527837273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30804436226228640351891515 46206654339342960527837273)
  ·
    refine ⟨34654990754507220395877955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46206654339342960527837273 34654990754507220395877955)
    ·
      refine ⟨51982486131760830593816933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34654990754507220395877955 51982486131760830593816933)
      ·
        refine ⟨9746716149705155736340675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51982486131760830593816933 9746716149705155736340675)
        ·
          refine ⟨14620074224557733604511013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9746716149705155736340675 14620074224557733604511013)
          ·
            refine ⟨2741263917104575050845815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14620074224557733604511013 2741263917104575050845815)
            ·
              refine ⟨4111895875656862576268723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741263917104575050845815 4111895875656862576268723)
              ·
                refine ⟨6167843813485293864403085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111895875656862576268723 6167843813485293864403085)
                ·
                  refine ⟨2312941430056985199151157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6167843813485293864403085 2312941430056985199151157)
                  ·
                    refine ⟨216838259067842362420421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2312941430056985199151157 216838259067842362420421)
                    ·
                      rfl

theorem cell23_1266873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_1266873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266873 prefixEnd_1266873 := by exact prefixLift 1266873
  have htrace : WordTrace (prefixWord ++ tailWord_1266873) baseStart_1266873 baseEnd_1266873 := by
    simpa [prefixWord, tailWord_1266873, baseEnd_1266873] using wordTrace_append hprefix tailTrace_1266873
  have hstable : (prefixWord ++ tailWord_1266873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266873).length < 2 ^ (prefixWord ++ tailWord_1266873).sum := by decide
  have hdescent : baseEnd_1266873 < baseStart_1266873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266903 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 4, 4]
def baseStart_1266903 : Nat := 118140960795 + 1266903 * 2 ^ 59
def prefixEnd_1266903 : Nat := 4983230072969 + 3 ^ 40 * 1266903 * 2
def baseEnd_1266903 : Nat := 216843393874387323295375

theorem tailTrace_1266903 : CollatzResearch.WordTrace tailWord_1266903 prefixEnd_1266903 216843393874387323295375 := by
  unfold tailWord_1266903
  simp only [CollatzResearch.WordTrace]
  refine ⟨46207748529234275651429363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30805165686156183767619575 46207748529234275651429363)
  ·
    refine ⟨69311622793851413477144045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46207748529234275651429363 69311622793851413477144045)
    ·
      refine ⟨25991858547694280053929017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69311622793851413477144045 25991858547694280053929017)
      ·
        refine ⟨19493893910770710040446763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25991858547694280053929017 19493893910770710040446763)
        ·
          refine ⟨29240840866156065060670145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19493893910770710040446763 29240840866156065060670145)
          ·
            refine ⟨21930630649617048795502609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29240840866156065060670145 21930630649617048795502609)
            ·
              refine ⟨16447972987212786596626957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21930630649617048795502609 16447972987212786596626957)
              ·
                refine ⟨6167989870204794973735109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16447972987212786596626957 6167989870204794973735109)
                ·
                  refine ⟨1156498100663399057575333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6167989870204794973735109 1156498100663399057575333)
                  ·
                    refine ⟨216843393874387323295375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1156498100663399057575333 216843393874387323295375)
                    ·
                      rfl

theorem cell23_1266903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_1266903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266903 prefixEnd_1266903 := by exact prefixLift 1266903
  have htrace : WordTrace (prefixWord ++ tailWord_1266903) baseStart_1266903 baseEnd_1266903 := by
    simpa [prefixWord, tailWord_1266903, baseEnd_1266903] using wordTrace_append hprefix tailTrace_1266903
  have hstable : (prefixWord ++ tailWord_1266903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266903).length < 2 ^ (prefixWord ++ tailWord_1266903).sum := by decide
  have hdescent : baseEnd_1266903 < baseStart_1266903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266904 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 1, 1, 3]
def baseStart_1266904 : Nat := 118140960795 + 1266904 * 2 ^ 59
def prefixEnd_1266904 : Nat := 4983230072969 + 3 ^ 40 * 1266904 * 2
def baseEnd_1266904 : Nat := 650530695103816465973621

theorem tailTrace_1266904 : CollatzResearch.WordTrace tailWord_1266904 prefixEnd_1266904 650530695103816465973621 := by
  unfold tailWord_1266904
  simp only [CollatzResearch.WordTrace]
  refine ⟨23103892501115326411107883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30805190001487101881477177 23103892501115326411107883)
  ·
    refine ⟨34655838751672989616661825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23103892501115326411107883 34655838751672989616661825)
    ·
      refine ⟨25991879063754742212496369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34655838751672989616661825 25991879063754742212496369)
      ·
        refine ⟨19493909297816056659372277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25991879063754742212496369 19493909297816056659372277)
        ·
          refine ⟨1827553996670255311816151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19493909297816056659372277 1827553996670255311816151)
          ·
            refine ⟨2741330995005382967724227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827553996670255311816151 2741330995005382967724227)
            ·
              refine ⟨4111996492508074451586341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741330995005382967724227 4111996492508074451586341)
              ·
                refine ⟨770999342345263959672439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4111996492508074451586341 770999342345263959672439)
                ·
                  refine ⟨1156499013517895939508659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770999342345263959672439 1156499013517895939508659)
                  ·
                    refine ⟨1734748520276843909262989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1156499013517895939508659 1734748520276843909262989)
                    ·
                      refine ⟨650530695103816465973621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734748520276843909262989 650530695103816465973621)
                      ·
                        rfl

theorem cell23_1266904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 1, 3].length) (baseStart_1266904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266904 prefixEnd_1266904 := by exact prefixLift 1266904
  have htrace : WordTrace (prefixWord ++ tailWord_1266904) baseStart_1266904 baseEnd_1266904 := by
    simpa [prefixWord, tailWord_1266904, baseEnd_1266904] using wordTrace_append hprefix tailTrace_1266904
  have hstable : (prefixWord ++ tailWord_1266904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266904).length < 2 ^ (prefixWord ++ tailWord_1266904).sum := by decide
  have hdescent : baseEnd_1266904 < baseStart_1266904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266920 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1266920 : Nat := 118140960795 + 1266920 * 2 ^ 59
def prefixEnd_1266920 : Nat := 4983230072969 + 3 ^ 40 * 1266920 * 2
def baseEnd_1266920 : Nat := 216846303598096134457849

theorem tailTrace_1266920 : CollatzResearch.WordTrace tailWord_1266920 prefixEnd_1266920 216846303598096134457849 := by
  unfold tailWord_1266920
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104184285086343777399107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30805579046781791703198809 23104184285086343777399107)
  ·
    refine ⟨34656276427629515666098661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23104184285086343777399107 34656276427629515666098661)
    ·
      refine ⟨6498051830180534187393499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34656276427629515666098661 6498051830180534187393499)
      ·
        refine ⟨9747077745270801281090249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6498051830180534187393499 9747077745270801281090249)
        ·
          refine ⟨7310308308953100960817687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9747077745270801281090249 7310308308953100960817687)
          ·
            refine ⟨10965462463429651441226531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7310308308953100960817687 10965462463429651441226531)
            ·
              refine ⟨16448193695144477161839797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10965462463429651441226531 16448193695144477161839797)
              ·
                refine ⟨1542018158919794733922481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16448193695144477161839797 1542018158919794733922481)
                ·
                  refine ⟨1156513619189846050441861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542018158919794733922481 1156513619189846050441861)
                  ·
                    refine ⟨216846303598096134457849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1156513619189846050441861 216846303598096134457849)
                    ·
                      rfl

theorem cell23_1266920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1266920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266920 prefixEnd_1266920 := by exact prefixLift 1266920
  have htrace : WordTrace (prefixWord ++ tailWord_1266920) baseStart_1266920 baseEnd_1266920 := by
    simpa [prefixWord, tailWord_1266920, baseEnd_1266920] using wordTrace_append hprefix tailTrace_1266920
  have hstable : (prefixWord ++ tailWord_1266920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266920).length < 2 ^ (prefixWord ++ tailWord_1266920).sum := by decide
  have hdescent : baseEnd_1266920 < baseStart_1266920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266923 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4]
def baseStart_1266923 : Nat := 118140960795 + 1266923 * 2 ^ 59
def prefixEnd_1266923 : Nat := 4983230072969 + 3 ^ 40 * 1266923 * 2
def baseEnd_1266923 : Nat := 650540451236251891636033

theorem tailTrace_1266923 : CollatzResearch.WordTrace tailWord_1266923 prefixEnd_1266923 650540451236251891636033 := by
  unfold tailWord_1266923
  simp only [CollatzResearch.WordTrace]
  refine ⟨46208477989161819067157423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30805651992774546044771615 46208477989161819067157423)
  ·
    refine ⟨69312716983742728600736135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46208477989161819067157423 69312716983742728600736135)
    ·
      refine ⟨103969075475614092901104203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69312716983742728600736135 103969075475614092901104203)
      ·
        refine ⟨155953613213421139351656305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103969075475614092901104203 155953613213421139351656305)
        ·
          refine ⟨116965209910065854513742229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155953613213421139351656305 116965209910065854513742229)
          ·
            refine ⟨5482744214534336930331667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116965209910065854513742229 5482744214534336930331667)
            ·
              refine ⟨8224116321801505395497501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482744214534336930331667 8224116321801505395497501)
              ·
                refine ⟨3084043620675564523311563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8224116321801505395497501 3084043620675564523311563)
                ·
                  refine ⟨4626065431013346784967345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084043620675564523311563 4626065431013346784967345)
                  ·
                    refine ⟨3469549073260010088725509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626065431013346784967345 3469549073260010088725509)
                    ·
                      refine ⟨650540451236251891636033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3469549073260010088725509 650540451236251891636033)
                      ·
                        rfl

theorem cell23_1266923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].length) (baseStart_1266923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266923 prefixEnd_1266923 := by exact prefixLift 1266923
  have htrace : WordTrace (prefixWord ++ tailWord_1266923) baseStart_1266923 baseEnd_1266923 := by
    simpa [prefixWord, tailWord_1266923, baseEnd_1266923] using wordTrace_append hprefix tailTrace_1266923
  have hstable : (prefixWord ++ tailWord_1266923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266923).length < 2 ^ (prefixWord ++ tailWord_1266923).sum := by decide
  have hdescent : baseEnd_1266923 < baseStart_1266923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1266947 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 1, 2, 3]
def baseStart_1266947 : Nat := 118140960795 + 1266947 * 2 ^ 59
def prefixEnd_1266947 : Nat := 4983230072969 + 3 ^ 40 * 1266947 * 2
def baseEnd_1266947 : Nat := 650552774771959797735923

theorem tailTrace_1266947 : CollatzResearch.WordTrace tailWord_1266947 prefixEnd_1266947 650552774771959797735923 := by
  unfold tailWord_1266947
  simp only [CollatzResearch.WordTrace]
  refine ⟨46209353341074871166031095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30806235560716580777354063 46209353341074871166031095)
  ·
    refine ⟨69314030011612306749046643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46209353341074871166031095 69314030011612306749046643)
    ·
      refine ⟨103971045017418460123569965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69314030011612306749046643 103971045017418460123569965)
      ·
        refine ⟨38989141881531922546338737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103971045017418460123569965 38989141881531922546338737)
        ·
          refine ⟨29241856411148941909754053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38989141881531922546338737 29241856411148941909754053)
          ·
            refine ⟨5482848077090426608078885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29241856411148941909754053 5482848077090426608078885)
            ·
              refine ⟨1028034014454454989014791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5482848077090426608078885 1028034014454454989014791)
              ·
                refine ⟨1542051021681682483522187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028034014454454989014791 1542051021681682483522187)
                ·
                  refine ⟨2313076532522523725283281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542051021681682483522187 2313076532522523725283281)
                  ·
                    refine ⟨1734807399391892793962461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313076532522523725283281 1734807399391892793962461)
                    ·
                      refine ⟨650552774771959797735923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1734807399391892793962461 650552774771959797735923)
                      ·
                        rfl

theorem cell23_1266947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_1266947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1266947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1266947 prefixEnd_1266947 := by exact prefixLift 1266947
  have htrace : WordTrace (prefixWord ++ tailWord_1266947) baseStart_1266947 baseEnd_1266947 := by
    simpa [prefixWord, tailWord_1266947, baseEnd_1266947] using wordTrace_append hprefix tailTrace_1266947
  have hstable : (prefixWord ++ tailWord_1266947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1266947).length < 2 ^ (prefixWord ++ tailWord_1266947).sum := by decide
  have hdescent : baseEnd_1266947 < baseStart_1266947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1266947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267000 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 3, 4, 2]
def baseStart_1267000 : Nat := 118140960795 + 1267000 * 2 ^ 59
def prefixEnd_1267000 : Nat := 4983230072969 + 3 ^ 40 * 1267000 * 2
def baseEnd_1267000 : Nat := 650579989246648090373179

theorem tailTrace_1267000 : CollatzResearch.WordTrace tailWord_1267000 prefixEnd_1267000 650579989246648090373179 := by
  unfold tailWord_1267000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23105643204941430608855227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30807524273255240811806969 23105643204941430608855227)
  ·
    refine ⟨34658464807412145913282841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23105643204941430608855227 34658464807412145913282841)
    ·
      refine ⟨25993848605559109434962131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34658464807412145913282841 25993848605559109434962131)
      ·
        refine ⟨38990772908338664152443197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25993848605559109434962131 38990772908338664152443197)
        ·
          refine ⟨14621539840626999057166199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38990772908338664152443197 14621539840626999057166199)
          ·
            refine ⟨21932309760940498585749299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14621539840626999057166199 21932309760940498585749299)
            ·
              refine ⟨32898464641410747878623949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21932309760940498585749299 32898464641410747878623949)
              ·
                refine ⟨12336924240529030454483981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32898464641410747878623949 12336924240529030454483981)
                ·
                  refine ⟨4626346590198386420431493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12336924240529030454483981 4626346590198386420431493)
                  ·
                    refine ⟨867439985662197453830905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4626346590198386420431493 867439985662197453830905)
                    ·
                      refine ⟨650579989246648090373179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867439985662197453830905 650579989246648090373179)
                      ·
                        rfl

theorem cell23_1267000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_1267000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267000 prefixEnd_1267000 := by exact prefixLift 1267000
  have htrace : WordTrace (prefixWord ++ tailWord_1267000) baseStart_1267000 baseEnd_1267000 := by
    simpa [prefixWord, tailWord_1267000, baseEnd_1267000] using wordTrace_append hprefix tailTrace_1267000
  have hstable : (prefixWord ++ tailWord_1267000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267000).length < 2 ^ (prefixWord ++ tailWord_1267000).sum := by decide
  have hdescent : baseEnd_1267000 < baseStart_1267000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267013 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_1267013 : Nat := 118140960795 + 1267013 * 2 ^ 59
def prefixEnd_1267013 : Nat := 4983230072969 + 3 ^ 40 * 1267013 * 2
def baseEnd_1267013 : Nat := 650586664495156539510619

theorem tailTrace_1267013 : CollatzResearch.WordTrace tailWord_1267013 prefixEnd_1267013 650586664495156539510619 := by
  unfold tailWord_1267013
  simp only [CollatzResearch.WordTrace]
  refine ⟨46211760558835764437933693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30807840372557176291955795 46211760558835764437933693)
  ·
    refine ⟨17329410209563411664225135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46211760558835764437933693 17329410209563411664225135)
    ·
      refine ⟨25994115314345117496337703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17329410209563411664225135 25994115314345117496337703)
      ·
        refine ⟨38991172971517676244506555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25994115314345117496337703 38991172971517676244506555)
        ·
          refine ⟨58486759457276514366759833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38991172971517676244506555 58486759457276514366759833)
          ·
            refine ⟨43865069592957385775069875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58486759457276514366759833 43865069592957385775069875)
            ·
              refine ⟨65797604389436078662604813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43865069592957385775069875 65797604389436078662604813)
              ·
                refine ⟨24674101646038529498476805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65797604389436078662604813 24674101646038529498476805)
                ·
                  refine ⟨4626394058632224280964401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24674101646038529498476805 4626394058632224280964401)
                  ·
                    refine ⟨3469795543974168210723301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626394058632224280964401 3469795543974168210723301)
                    ·
                      refine ⟨650586664495156539510619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3469795543974168210723301 650586664495156539510619)
                      ·
                        rfl

theorem cell23_1267013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_1267013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267013 prefixEnd_1267013 := by exact prefixLift 1267013
  have htrace : WordTrace (prefixWord ++ tailWord_1267013) baseStart_1267013 baseEnd_1267013 := by
    simpa [prefixWord, tailWord_1267013, baseEnd_1267013] using wordTrace_append hprefix tailTrace_1267013
  have hstable : (prefixWord ++ tailWord_1267013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267013).length < 2 ^ (prefixWord ++ tailWord_1267013).sum := by decide
  have hdescent : baseEnd_1267013 < baseStart_1267013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267017 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 4, 2, 2]
def baseStart_1267017 : Nat := 118140960795 + 1267017 * 2 ^ 59
def prefixEnd_1267017 : Nat := 4983230072969 + 3 ^ 40 * 1267017 * 2
def baseEnd_1267017 : Nat := 650588718417774523860601

theorem tailTrace_1267017 : CollatzResearch.WordTrace tailWord_1267017 prefixEnd_1267017 650588718417774523860601 := by
  unfold tailWord_1267017
  simp only [CollatzResearch.WordTrace]
  refine ⟨46211906450821273121079305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30807937633880848747386203 46211906450821273121079305)
  ·
    refine ⟨34658929838115954840809479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46211906450821273121079305 34658929838115954840809479)
    ·
      refine ⟨51988394757173932261214219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34658929838115954840809479 51988394757173932261214219)
      ·
        refine ⟨77982592135760898391821329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51988394757173932261214219 77982592135760898391821329)
        ·
          refine ⟨58486944101820673793865997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77982592135760898391821329 58486944101820673793865997)
          ·
            refine ⟨21932604038182752672699749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58486944101820673793865997 21932604038182752672699749)
            ·
              refine ⟨4112363257159266126131203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21932604038182752672699749 4112363257159266126131203)
              ·
                refine ⟨6168544885738899189196805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112363257159266126131203 6168544885738899189196805)
                ·
                  refine ⟨1156602166076043597974401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6168544885738899189196805 1156602166076043597974401)
                  ·
                    refine ⟨867451624557032698480801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156602166076043597974401 867451624557032698480801)
                    ·
                      refine ⟨650588718417774523860601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867451624557032698480801 650588718417774523860601)
                      ·
                        rfl

theorem cell23_1267017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 2, 2].length) (baseStart_1267017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267017 prefixEnd_1267017 := by exact prefixLift 1267017
  have htrace : WordTrace (prefixWord ++ tailWord_1267017) baseStart_1267017 baseEnd_1267017 := by
    simpa [prefixWord, tailWord_1267017, baseEnd_1267017] using wordTrace_append hprefix tailTrace_1267017
  have hstable : (prefixWord ++ tailWord_1267017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267017).length < 2 ^ (prefixWord ++ tailWord_1267017).sum := by decide
  have hdescent : baseEnd_1267017 < baseStart_1267017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267063 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_1267063 : Nat := 118140960795 + 1267063 * 2 ^ 59
def prefixEnd_1267063 : Nat := 4983230072969 + 3 ^ 40 * 1267063 * 2
def baseEnd_1267063 : Nat := 650612338527881343885389

theorem tailTrace_1267063 : CollatzResearch.WordTrace tailWord_1267063 prefixEnd_1267063 650612338527881343885389 := by
  unfold tailWord_1267063
  simp only [CollatzResearch.WordTrace]
  refine ⟨46213584208654622977253843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30809056139103081984835895 46213584208654622977253843)
  ·
    refine ⟨69320376312981934465880765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46213584208654622977253843 69320376312981934465880765)
    ·
      refine ⟨25995141117368225424705287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69320376312981934465880765 25995141117368225424705287)
      ·
        refine ⟨38992711676052338137057931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25995141117368225424705287 38992711676052338137057931)
        ·
          refine ⟨58489067514078507205586897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38992711676052338137057931 58489067514078507205586897)
          ·
            refine ⟨43866800635558880404190173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58489067514078507205586897 43866800635558880404190173)
            ·
              refine ⟨16450050238334580151571315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43866800635558880404190173 16450050238334580151571315)
              ·
                refine ⟨24675075357501870227356973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16450050238334580151571315 24675075357501870227356973)
                ·
                  refine ⟨9253153259063201335258865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24675075357501870227356973 9253153259063201335258865)
                  ·
                    refine ⟨6939864944297401001444149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9253153259063201335258865 6939864944297401001444149)
                    ·
                      refine ⟨650612338527881343885389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6939864944297401001444149 650612338527881343885389)
                      ·
                        rfl

theorem cell23_1267063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_1267063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267063 prefixEnd_1267063 := by exact prefixLift 1267063
  have htrace : WordTrace (prefixWord ++ tailWord_1267063) baseStart_1267063 baseEnd_1267063 := by
    simpa [prefixWord, tailWord_1267063, baseEnd_1267063] using wordTrace_append hprefix tailTrace_1267063
  have hstable : (prefixWord ++ tailWord_1267063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267063).length < 2 ^ (prefixWord ++ tailWord_1267063).sum := by decide
  have hdescent : baseEnd_1267063 < baseStart_1267063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267080 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1267080 : Nat := 118140960795 + 1267080 * 2 ^ 59
def prefixEnd_1267080 : Nat := 4983230072969 + 3 ^ 40 * 1267080 * 2
def baseEnd_1267080 : Nat := 650621067699007777372811

theorem tailTrace_1267080 : CollatzResearch.WordTrace tailWord_1267080 prefixEnd_1267080 650621067699007777372811 := by
  unfold tailWord_1267080
  simp only [CollatzResearch.WordTrace]
  refine ⟨23107102124796517440311347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30809469499728689920415129 23107102124796517440311347)
  ·
    refine ⟨34660653187194776160467021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23107102124796517440311347 34660653187194776160467021)
    ·
      refine ⟨12997744945198041060175133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34660653187194776160467021 12997744945198041060175133)
      ·
        refine ⟨4874154354449265397565675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12997744945198041060175133 4874154354449265397565675)
        ·
          refine ⟨7311231531673898096348513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874154354449265397565675 7311231531673898096348513)
          ·
            refine ⟨5483423648755423572261385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311231531673898096348513 5483423648755423572261385)
            ·
              refine ⟨4112567736566567679196039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483423648755423572261385 4112567736566567679196039)
              ·
                refine ⟨6168851604849851518794059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112567736566567679196039 6168851604849851518794059)
                ·
                  refine ⟨9253277407274777278191089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6168851604849851518794059 9253277407274777278191089)
                  ·
                    refine ⟨6939958055456082958643317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9253277407274777278191089 6939958055456082958643317)
                    ·
                      refine ⟨650621067699007777372811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6939958055456082958643317 650621067699007777372811)
                      ·
                        rfl

theorem cell23_1267080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1267080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267080 prefixEnd_1267080 := by exact prefixLift 1267080
  have htrace : WordTrace (prefixWord ++ tailWord_1267080) baseStart_1267080 baseEnd_1267080 := by
    simpa [prefixWord, tailWord_1267080, baseEnd_1267080] using wordTrace_append hprefix tailTrace_1267080
  have hstable : (prefixWord ++ tailWord_1267080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267080).length < 2 ^ (prefixWord ++ tailWord_1267080).sum := by decide
  have hdescent : baseEnd_1267080 < baseStart_1267080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267160 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_1267160 : Nat := 118140960795 + 1267160 * 2 ^ 59
def prefixEnd_1267160 : Nat := 4983230072969 + 3 ^ 40 * 1267160 * 2
def baseEnd_1267160 : Nat := 216887382050455821457481

theorem tailTrace_1267160 : CollatzResearch.WordTrace tailWord_1267160 prefixEnd_1267160 216887382050455821457481 := by
  unfold tailWord_1267160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23108561044651604271767467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30811414726202139029023289 23108561044651604271767467)
  ·
    refine ⟨34662841566977406407651201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23108561044651604271767467 34662841566977406407651201)
    ·
      refine ⟨25997131175233054805738401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34662841566977406407651201 25997131175233054805738401)
      ·
        refine ⟨19497848381424791104303801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25997131175233054805738401 19497848381424791104303801)
        ·
          refine ⟨14623386286068593328227851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19497848381424791104303801 14623386286068593328227851)
          ·
            refine ⟨21935079429102889992341777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14623386286068593328227851 21935079429102889992341777)
            ·
              refine ⟨16451309571827167494256333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21935079429102889992341777 16451309571827167494256333)
              ·
                refine ⟨6169241089435187810346125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16451309571827167494256333 6169241089435187810346125)
                ·
                  refine ⟨2313465408538195428879797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6169241089435187810346125 2313465408538195428879797)
                  ·
                    refine ⟨216887382050455821457481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2313465408538195428879797 216887382050455821457481)
                    ·
                      rfl

theorem cell23_1267160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_1267160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267160 prefixEnd_1267160 := by exact prefixLift 1267160
  have htrace : WordTrace (prefixWord ++ tailWord_1267160) baseStart_1267160 baseEnd_1267160 := by
    simpa [prefixWord, tailWord_1267160, baseEnd_1267160] using wordTrace_append hprefix tailTrace_1267160
  have hstable : (prefixWord ++ tailWord_1267160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267160).length < 2 ^ (prefixWord ++ tailWord_1267160).sum := by decide
  have hdescent : baseEnd_1267160 < baseStart_1267160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267167 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 1, 5, 2]
def baseStart_1267167 : Nat := 118140960795 + 1267167 * 2 ^ 59
def prefixEnd_1267167 : Nat := 4983230072969 + 3 ^ 40 * 1267167 * 2
def baseEnd_1267167 : Nat := 650665740515948936984911

theorem tailTrace_1267167 : CollatzResearch.WordTrace tailWord_1267167 prefixEnd_1267167 650665740515948936984911 := by
  unfold tailWord_1267167
  simp only [CollatzResearch.WordTrace]
  refine ⟨46217377400277848739039755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30811584933518565826026503 46217377400277848739039755)
  ·
    refine ⟨69326066100416773108559633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46217377400277848739039755 69326066100416773108559633)
    ·
      refine ⟨51994549575312579831419725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69326066100416773108559633 51994549575312579831419725)
      ·
        refine ⟨19497956090742217436782397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51994549575312579831419725 19497956090742217436782397)
        ·
          refine ⟨7311733534028331538793399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19497956090742217436782397 7311733534028331538793399)
          ·
            refine ⟨10967600301042497308190099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311733534028331538793399 10967600301042497308190099)
            ·
              refine ⟨16451400451563745962285149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10967600301042497308190099 16451400451563745962285149)
              ·
                refine ⟨6169275169336404735856931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16451400451563745962285149 6169275169336404735856931)
                ·
                  refine ⟨9253912754004607103785397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169275169336404735856931 9253912754004607103785397)
                  ·
                    refine ⟨867554320687931915979881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9253912754004607103785397 867554320687931915979881)
                    ·
                      refine ⟨650665740515948936984911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867554320687931915979881 650665740515948936984911)
                      ·
                        rfl

theorem cell23_1267167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_1267167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267167 prefixEnd_1267167 := by exact prefixLift 1267167
  have htrace : WordTrace (prefixWord ++ tailWord_1267167) baseStart_1267167 baseEnd_1267167 := by
    simpa [prefixWord, tailWord_1267167, baseEnd_1267167] using wordTrace_append hprefix tailTrace_1267167
  have hstable : (prefixWord ++ tailWord_1267167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267167).length < 2 ^ (prefixWord ++ tailWord_1267167).sum := by decide
  have hdescent : baseEnd_1267167 < baseStart_1267167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267184 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 2, 3, 2]
def baseStart_1267184 : Nat := 118140960795 + 1267184 * 2 ^ 59
def prefixEnd_1267184 : Nat := 4983230072969 + 3 ^ 40 * 1267184 * 2
def baseEnd_1267184 : Nat := 650674469687075370472333

theorem tailTrace_1267184 : CollatzResearch.WordTrace tailWord_1267184 prefixEnd_1267184 650674469687075370472333 := by
  unfold tailWord_1267184
  simp only [CollatzResearch.WordTrace]
  refine ⟨23108998720608130321204303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30811998294144173761605737 23108998720608130321204303)
  ·
    refine ⟨34663498080912195481806455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23108998720608130321204303 34663498080912195481806455)
    ·
      refine ⟨51995247121368293222709683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34663498080912195481806455 51995247121368293222709683)
      ·
        refine ⟨77992870682052439834064525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51995247121368293222709683 77992870682052439834064525)
        ·
          refine ⟨29247326505769664937774197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77992870682052439834064525 29247326505769664937774197)
          ·
            refine ⟨2741936859915906087916331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29247326505769664937774197 2741936859915906087916331)
            ·
              refine ⟨4112905289873859131874497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741936859915906087916331 4112905289873859131874497)
              ·
                refine ⟨3084678967405394348905873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112905289873859131874497 3084678967405394348905873)
                ·
                  refine ⟨2313509225554045761679405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084678967405394348905873 2313509225554045761679405)
                  ·
                    refine ⟨867565959582767160629777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313509225554045761679405 867565959582767160629777)
                    ·
                      refine ⟨650674469687075370472333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867565959582767160629777 650674469687075370472333)
                      ·
                        rfl

theorem cell23_1267184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 3, 2].length) (baseStart_1267184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267184 prefixEnd_1267184 := by exact prefixLift 1267184
  have htrace : WordTrace (prefixWord ++ tailWord_1267184) baseStart_1267184 baseEnd_1267184 := by
    simpa [prefixWord, tailWord_1267184, baseEnd_1267184] using wordTrace_append hprefix tailTrace_1267184
  have hstable : (prefixWord ++ tailWord_1267184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267184).length < 2 ^ (prefixWord ++ tailWord_1267184).sum := by decide
  have hdescent : baseEnd_1267184 < baseStart_1267184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267198 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1267198 : Nat := 118140960795 + 1267198 * 2 ^ 59
def prefixEnd_1267198 : Nat := 4983230072969 + 3 ^ 40 * 1267198 * 2
def baseEnd_1267198 : Nat := 72297962046248701744141

theorem tailTrace_1267198 : CollatzResearch.WordTrace tailWord_1267198 prefixEnd_1267198 72297962046248701744141 := by
  unfold tailWord_1267198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777313507895692629177281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30812338708777027355612165 5777313507895692629177281)
  ·
    refine ⟨4332985130921769471882961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5777313507895692629177281 4332985130921769471882961)
    ·
      refine ⟨3249738848191327103912221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4332985130921769471882961 3249738848191327103912221)
      ·
        refine ⟨1218652068071747663967083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3249738848191327103912221 1218652068071747663967083)
        ·
          refine ⟨1827978102107621495950625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218652068071747663967083 1827978102107621495950625)
          ·
            refine ⟨1370983576580716121962969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827978102107621495950625 1370983576580716121962969)
            ·
              refine ⟨1028237682435537091472227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370983576580716121962969 1028237682435537091472227)
              ·
                refine ⟨1542356523653305637208341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028237682435537091472227 1542356523653305637208341)
                ·
                  refine ⟨72297962046248701744141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1542356523653305637208341 72297962046248701744141)
                  ·
                    rfl

theorem cell23_1267198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1267198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267198 prefixEnd_1267198 := by exact prefixLift 1267198
  have htrace : WordTrace (prefixWord ++ tailWord_1267198) baseStart_1267198 baseEnd_1267198 := by
    simpa [prefixWord, tailWord_1267198, baseEnd_1267198] using wordTrace_append hprefix tailTrace_1267198
  have hstable : (prefixWord ++ tailWord_1267198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267198).length < 2 ^ (prefixWord ++ tailWord_1267198).sum := by decide
  have hdescent : baseEnd_1267198 < baseStart_1267198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267211 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 1, 5]
def baseStart_1267211 : Nat := 118140960795 + 1267211 * 2 ^ 59
def prefixEnd_1267211 : Nat := 4983230072969 + 3 ^ 40 * 1267211 * 2
def baseEnd_1267211 : Nat := 216896111221582254944903

theorem tailTrace_1267211 : CollatzResearch.WordTrace tailWord_1267211 prefixEnd_1267211 216896111221582254944903 := by
  unfold tailWord_1267211
  simp only [CollatzResearch.WordTrace]
  refine ⟨46218982212118444253641487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30812654808078962835760991 46218982212118444253641487)
  ·
    refine ⟨69328473318177666380462231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46218982212118444253641487 69328473318177666380462231)
    ·
      refine ⟨103992709977266499570693347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69328473318177666380462231 103992709977266499570693347)
      ·
        refine ⟨155989064965899749356040021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103992709977266499570693347 155989064965899749356040021)
        ·
          refine ⟨913998427534568843883047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 155989064965899749356040021 913998427534568843883047)
          ·
            refine ⟨1370997641301853265824571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913998427534568843883047 1370997641301853265824571)
            ·
              refine ⟨2056496461952779898736857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370997641301853265824571 2056496461952779898736857)
              ·
                refine ⟨1542372346464584924052643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2056496461952779898736857 1542372346464584924052643)
                ·
                  refine ⟨2313558519696877386078965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542372346464584924052643 2313558519696877386078965)
                  ·
                    refine ⟨216896111221582254944903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2313558519696877386078965 216896111221582254944903)
                    ·
                      rfl

theorem cell23_1267211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 5].length) (baseStart_1267211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267211 prefixEnd_1267211 := by exact prefixLift 1267211
  have htrace : WordTrace (prefixWord ++ tailWord_1267211) baseStart_1267211 baseEnd_1267211 := by
    simpa [prefixWord, tailWord_1267211, baseEnd_1267211] using wordTrace_append hprefix tailTrace_1267211
  have hstable : (prefixWord ++ tailWord_1267211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267211).length < 2 ^ (prefixWord ++ tailWord_1267211).sum := by decide
  have hdescent : baseEnd_1267211 < baseStart_1267211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267214 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1267214 : Nat := 118140960795 + 1267214 * 2 ^ 59
def prefixEnd_1267214 : Nat := 4983230072969 + 3 ^ 40 * 1267214 * 2
def baseEnd_1267214 : Nat := 650689874106710253097195

theorem tailTrace_1267214 : CollatzResearch.WordTrace tailWord_1267214 prefixEnd_1267214 650689874106710253097195 := by
  unfold tailWord_1267214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777386453888446970750087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30812727754071717177333797 5777386453888446970750087)
  ·
    refine ⟨8666079680832670456125131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5777386453888446970750087 8666079680832670456125131)
    ·
      refine ⟨12999119521249005684187697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8666079680832670456125131 12999119521249005684187697)
      ·
        refine ⟨9749339640936754263140773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12999119521249005684187697 9749339640936754263140773)
        ·
          refine ⟨1828001182675641424338895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9749339640936754263140773 1828001182675641424338895)
          ·
            refine ⟨2742001774013462136508343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828001182675641424338895 2742001774013462136508343)
            ·
              refine ⟨4113002661020193204762515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742001774013462136508343 4113002661020193204762515)
              ·
                refine ⟨6169503991530289807143773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113002661020193204762515 6169503991530289807143773)
                ·
                  refine ⟨2313563996823858677678915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6169503991530289807143773 2313563996823858677678915)
                  ·
                    refine ⟨3470345995235788016518373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2313563996823858677678915 3470345995235788016518373)
                    ·
                      refine ⟨650689874106710253097195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3470345995235788016518373 650689874106710253097195)
                      ·
                        rfl

theorem cell23_1267214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1267214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267214 prefixEnd_1267214 := by exact prefixLift 1267214
  have htrace : WordTrace (prefixWord ++ tailWord_1267214) baseStart_1267214 baseEnd_1267214 := by
    simpa [prefixWord, tailWord_1267214, baseEnd_1267214] using wordTrace_append hprefix tailTrace_1267214
  have hstable : (prefixWord ++ tailWord_1267214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267214).length < 2 ^ (prefixWord ++ tailWord_1267214).sum := by decide
  have hdescent : baseEnd_1267214 < baseStart_1267214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267217 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_1267217 : Nat := 118140960795 + 1267217 * 2 ^ 59
def prefixEnd_1267217 : Nat := 4983230072969 + 3 ^ 40 * 1267217 * 2
def baseEnd_1267217 : Nat := 650691414548673741359681

theorem tailTrace_1267217 : CollatzResearch.WordTrace tailWord_1267217 prefixEnd_1267217 650691414548673741359681 := by
  unfold tailWord_1267217
  simp only [CollatzResearch.WordTrace]
  refine ⟨46219201050096707278359905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30812800700064471518906603 46219201050096707278359905)
  ·
    refine ⟨34664400787572530458769929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46219201050096707278359905 34664400787572530458769929)
    ·
      refine ⟨25998300590679397844077447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34664400787572530458769929 25998300590679397844077447)
      ·
        refine ⟨38997450886019096766116171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25998300590679397844077447 38997450886019096766116171)
        ·
          refine ⟨58496176329028645149174257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38997450886019096766116171 58496176329028645149174257)
          ·
            refine ⟨43872132246771483861880693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58496176329028645149174257 43872132246771483861880693)
            ·
              refine ⟨4113012398134826612051315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43872132246771483861880693 4113012398134826612051315)
              ·
                refine ⟨6169518597202239918076973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113012398134826612051315 6169518597202239918076973)
                ·
                  refine ⟨2313569473950839969278865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6169518597202239918076973 2313569473950839969278865)
                  ·
                    refine ⟨1735177105463129976959149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313569473950839969278865 1735177105463129976959149)
                    ·
                      refine ⟨650691414548673741359681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1735177105463129976959149 650691414548673741359681)
                      ·
                        rfl

theorem cell23_1267217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_1267217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267217 prefixEnd_1267217 := by exact prefixLift 1267217
  have htrace : WordTrace (prefixWord ++ tailWord_1267217) baseStart_1267217 baseEnd_1267217 := by
    simpa [prefixWord, tailWord_1267217, baseEnd_1267217] using wordTrace_append hprefix tailTrace_1267217
  have hstable : (prefixWord ++ tailWord_1267217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267217).length < 2 ^ (prefixWord ++ tailWord_1267217).sum := by decide
  have hdescent : baseEnd_1267217 < baseStart_1267217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267234 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1267234 : Nat := 118140960795 + 1267234 * 2 ^ 59
def prefixEnd_1267234 : Nat := 4983230072969 + 3 ^ 40 * 1267234 * 2
def baseEnd_1267234 : Nat := 650700143719800174847103

theorem tailTrace_1267234 : CollatzResearch.WordTrace tailWord_1267234 prefixEnd_1267234 650700143719800174847103 := by
  unfold tailWord_1267234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554955272758779795432189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30813214060690079454485837 11554955272758779795432189)
  ·
    refine ⟨4333108227284542423287071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11554955272758779795432189 4333108227284542423287071)
    ·
      refine ⟨6499662340926813634930607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4333108227284542423287071 6499662340926813634930607)
      ·
        refine ⟨9749493511390220452395911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6499662340926813634930607 9749493511390220452395911)
        ·
          refine ⟨14624240267085330678593867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9749493511390220452395911 14624240267085330678593867)
          ·
            refine ⟨21936360400627996017890801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14624240267085330678593867 21936360400627996017890801)
            ·
              refine ⟨16452270300470997013418101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21936360400627996017890801 16452270300470997013418101)
              ·
                refine ⟨1542400340669155970007947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16452270300470997013418101 1542400340669155970007947)
                ·
                  refine ⟨2313600511003733955011921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542400340669155970007947 2313600511003733955011921)
                  ·
                    refine ⟨1735200383252800466258941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313600511003733955011921 1735200383252800466258941)
                    ·
                      refine ⟨650700143719800174847103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1735200383252800466258941 650700143719800174847103)
                      ·
                        rfl

theorem cell23_1267234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1267234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267234 prefixEnd_1267234 := by exact prefixLift 1267234
  have htrace : WordTrace (prefixWord ++ tailWord_1267234) baseStart_1267234 baseEnd_1267234 := by
    simpa [prefixWord, tailWord_1267234, baseEnd_1267234] using wordTrace_append hprefix tailTrace_1267234
  have hstable : (prefixWord ++ tailWord_1267234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267234).length < 2 ^ (prefixWord ++ tailWord_1267234).sum := by decide
  have hdescent : baseEnd_1267234 < baseStart_1267234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267274 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2]
def baseStart_1267274 : Nat := 118140960795 + 1267274 * 2 ^ 59
def prefixEnd_1267274 : Nat := 4983230072969 + 3 ^ 40 * 1267274 * 2
def baseEnd_1267274 : Nat := 650720682945980018346919

theorem tailTrace_1267274 : CollatzResearch.WordTrace tailWord_1267274 prefixEnd_1267274 650720682945980018346919 := by
  unfold tailWord_1267274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11555320002722551503296219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30814186673926804008789917 11555320002722551503296219)
  ·
    refine ⟨17332980004083827254944329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11555320002722551503296219 17332980004083827254944329)
    ·
      refine ⟨12999735003062870441208247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17332980004083827254944329 12999735003062870441208247)
      ·
        refine ⟨19499602504594305661812371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12999735003062870441208247 19499602504594305661812371)
        ·
          refine ⟨29249403756891458492718557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19499602504594305661812371 29249403756891458492718557)
          ·
            refine ⟨10968526408834296934769459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29249403756891458492718557 10968526408834296934769459)
            ·
              refine ⟨16452789613251445402154189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10968526408834296934769459 16452789613251445402154189)
              ·
                refine ⟨6169796104969292025807821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16452789613251445402154189 6169796104969292025807821)
                ·
                  refine ⟨2313673539363484509677933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6169796104969292025807821 2313673539363484509677933)
                  ·
                    refine ⟨867627577261306691129225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313673539363484509677933 867627577261306691129225)
                    ·
                      refine ⟨650720682945980018346919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867627577261306691129225 650720682945980018346919)
                      ·
                        rfl

theorem cell23_1267274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_1267274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267274 prefixEnd_1267274 := by exact prefixLift 1267274
  have htrace : WordTrace (prefixWord ++ tailWord_1267274) baseStart_1267274 baseEnd_1267274 := by
    simpa [prefixWord, tailWord_1267274, baseEnd_1267274] using wordTrace_append hprefix tailTrace_1267274
  have hstable : (prefixWord ++ tailWord_1267274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267274).length < 2 ^ (prefixWord ++ tailWord_1267274).sum := by decide
  have hdescent : baseEnd_1267274 < baseStart_1267274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267280 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_1267280 : Nat := 118140960795 + 1267280 * 2 ^ 59
def prefixEnd_1267280 : Nat := 4983230072969 + 3 ^ 40 * 1267280 * 2
def baseEnd_1267280 : Nat := 216907921276635664957297

theorem tailTrace_1267280 : CollatzResearch.WordTrace tailWord_1267280 prefixEnd_1267280 216907921276635664957297 := by
  unfold tailWord_1267280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23110749424434234518951647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30814332565912312691935529 23110749424434234518951647)
  ·
    refine ⟨34666124136651351778427471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23110749424434234518951647 34666124136651351778427471)
    ·
      refine ⟨51999186204977027667641207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34666124136651351778427471 51999186204977027667641207)
      ·
        refine ⟨77998779307465541501461811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51999186204977027667641207 77998779307465541501461811)
        ·
          refine ⟨116998168961198312252192717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77998779307465541501461811 116998168961198312252192717)
          ·
            refine ⟨43874313360449367094572269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116998168961198312252192717 43874313360449367094572269)
            ·
              refine ⟨16452867510168512660464601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43874313360449367094572269 16452867510168512660464601)
              ·
                refine ⟨12339650632626384495348451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16452867510168512660464601 12339650632626384495348451)
                ·
                  refine ⟨18509475948939576743022677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12339650632626384495348451 18509475948939576743022677)
                  ·
                    refine ⟨216907921276635664957297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18509475948939576743022677 216907921276635664957297)
                    ·
                      rfl

theorem cell23_1267280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_1267280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267280 prefixEnd_1267280 := by exact prefixLift 1267280
  have htrace : WordTrace (prefixWord ++ tailWord_1267280) baseStart_1267280 baseEnd_1267280 := by
    simpa [prefixWord, tailWord_1267280, baseEnd_1267280] using wordTrace_append hprefix tailTrace_1267280
  have hstable : (prefixWord ++ tailWord_1267280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267280).length < 2 ^ (prefixWord ++ tailWord_1267280).sum := by decide
  have hdescent : baseEnd_1267280 < baseStart_1267280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267337 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_1267337 : Nat := 118140960795 + 1267337 * 2 ^ 59
def prefixEnd_1267337 : Nat := 4983230072969 + 3 ^ 40 * 1267337 * 2
def baseEnd_1267337 : Nat := 650753032227213271859129

theorem tailTrace_1267337 : CollatzResearch.WordTrace tailWord_1267337 prefixEnd_1267337 650753032227213271859129 := by
  unfold tailWord_1267337
  simp only [CollatzResearch.WordTrace]
  refine ⟨46223577809661967772728265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30815718539774645181818843 46223577809661967772728265)
  ·
    refine ⟨34667683357246475829546199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46223577809661967772728265 34667683357246475829546199)
    ·
      refine ⟨52001525035869713744319299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34667683357246475829546199 52001525035869713744319299)
      ·
        refine ⟨78002287553804570616478949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52001525035869713744319299 78002287553804570616478949)
        ·
          refine ⟨14625428916338356990589803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78002287553804570616478949 14625428916338356990589803)
          ·
            refine ⟨21938143374507535485884705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14625428916338356990589803 21938143374507535485884705)
            ·
              refine ⟨16453607530880651614413529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21938143374507535485884705 16453607530880651614413529)
              ·
                refine ⟨12340205648160488710810147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16453607530880651614413529 12340205648160488710810147)
                ·
                  refine ⟨18510308472240733066215221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12340205648160488710810147 18510308472240733066215221)
                  ·
                    refine ⟨1735341419272568724957677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18510308472240733066215221 1735341419272568724957677)
                    ·
                      refine ⟨650753032227213271859129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1735341419272568724957677 650753032227213271859129)
                      ·
                        rfl

theorem cell23_1267337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_1267337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267337 prefixEnd_1267337 := by exact prefixLift 1267337
  have htrace : WordTrace (prefixWord ++ tailWord_1267337) baseStart_1267337 baseEnd_1267337 := by
    simpa [prefixWord, tailWord_1267337, baseEnd_1267337] using wordTrace_append hprefix tailTrace_1267337
  have hstable : (prefixWord ++ tailWord_1267337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267337).length < 2 ^ (prefixWord ++ tailWord_1267337).sum := by decide
  have hdescent : baseEnd_1267337 < baseStart_1267337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267434 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_1267434 : Nat := 118140960795 + 1267434 * 2 ^ 59
def prefixEnd_1267434 : Nat := 4983230072969 + 3 ^ 40 * 1267434 * 2
def baseEnd_1267434 : Nat := 72311426650077710260687

theorem tailTrace_1267434 : CollatzResearch.WordTrace tailWord_1267434 prefixEnd_1267434 72311426650077710260687 := by
  unfold tailWord_1267434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556778922577638334752339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30818077126873702226006237 11556778922577638334752339)
  ·
    refine ⟨17335168383866457502128509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11556778922577638334752339 17335168383866457502128509)
    ·
      refine ⟨6500688143949921563298191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17335168383866457502128509 6500688143949921563298191)
      ·
        refine ⟨9751032215924882344947287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6500688143949921563298191 9751032215924882344947287)
        ·
          refine ⟨14626548323887323517420931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751032215924882344947287 14626548323887323517420931)
          ·
            refine ⟨21939822485830985276131397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14626548323887323517420931 21939822485830985276131397)
            ·
              refine ⟨4113716716093309739274637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21939822485830985276131397 4113716716093309739274637)
              ·
                refine ⟨1542643768534991152227989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113716716093309739274637 1542643768534991152227989)
                ·
                  refine ⟨72311426650077710260687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1542643768534991152227989 72311426650077710260687)
                  ·
                    rfl

theorem cell23_1267434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_1267434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267434 prefixEnd_1267434 := by exact prefixLift 1267434
  have htrace : WordTrace (prefixWord ++ tailWord_1267434) baseStart_1267434 baseEnd_1267434 := by
    simpa [prefixWord, tailWord_1267434, baseEnd_1267434] using wordTrace_append hprefix tailTrace_1267434
  have hstable : (prefixWord ++ tailWord_1267434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267434).length < 2 ^ (prefixWord ++ tailWord_1267434).sum := by decide
  have hdescent : baseEnd_1267434 < baseStart_1267434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267518 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1267518 : Nat := 118140960795 + 1267518 * 2 ^ 59
def prefixEnd_1267518 : Nat := 4983230072969 + 3 ^ 40 * 1267518 * 2
def baseEnd_1267518 : Nat := 650845972225677063695797

theorem tailTrace_1267518 : CollatzResearch.WordTrace tailWord_1267518 prefixEnd_1267518 650845972225677063695797 := by
  unfold tailWord_1267518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778772427750779460633401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30820119614670823790044805 5778772427750779460633401)
  ·
    refine ⟨4334079320813084595475051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5778772427750779460633401 4334079320813084595475051)
    ·
      refine ⟨6501118981219626893212577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4334079320813084595475051 6501118981219626893212577)
      ·
        refine ⟨4875839235914720169909433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6501118981219626893212577 4875839235914720169909433)
        ·
          refine ⟨3656879426936040127432075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4875839235914720169909433 3656879426936040127432075)
          ·
            refine ⟨5485319140404060191148113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656879426936040127432075 5485319140404060191148113)
            ·
              refine ⟨4113989355303045143361085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485319140404060191148113 4113989355303045143361085)
              ·
                refine ⟨1542746008238641928760407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113989355303045143361085 1542746008238641928760407)
                ·
                  refine ⟨2314119012357962893140611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542746008238641928760407 2314119012357962893140611)
                  ·
                    refine ⟨3471178518536944339710917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2314119012357962893140611 3471178518536944339710917)
                    ·
                      refine ⟨650845972225677063695797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3471178518536944339710917 650845972225677063695797)
                      ·
                        rfl

theorem cell23_1267518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1267518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267518 prefixEnd_1267518 := by exact prefixLift 1267518
  have htrace : WordTrace (prefixWord ++ tailWord_1267518) baseStart_1267518 baseEnd_1267518 := by
    simpa [prefixWord, tailWord_1267518, baseEnd_1267518] using wordTrace_append hprefix tailTrace_1267518
  have hstable : (prefixWord ++ tailWord_1267518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267518).length < 2 ^ (prefixWord ++ tailWord_1267518).sum := by decide
  have hdescent : baseEnd_1267518 < baseStart_1267518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267555 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 3]
def baseStart_1267555 : Nat := 118140960795 + 1267555 * 2 ^ 59
def prefixEnd_1267555 : Nat := 4983230072969 + 3 ^ 40 * 1267555 * 2
def baseEnd_1267555 : Nat := 650864971009893418933127

theorem tailTrace_1267555 : CollatzResearch.WordTrace tailWord_1267555 prefixEnd_1267555 650864971009893418933127 := by
  unfold tailWord_1267555
  simp only [CollatzResearch.WordTrace]
  refine ⟨46231528922872191004164119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30821019281914794002776079 46231528922872191004164119)
  ·
    refine ⟨69347293384308286506246179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46231528922872191004164119 69347293384308286506246179)
    ·
      refine ⟨104020940076462429759369269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69347293384308286506246179 104020940076462429759369269)
      ·
        refine ⟨9751963132168352789940869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104020940076462429759369269 9751963132168352789940869)
        ·
          refine ⟨1828493087281566148113913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9751963132168352789940869 1828493087281566148113913)
          ·
            refine ⟨1371369815461174611085435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828493087281566148113913 1371369815461174611085435)
            ·
              refine ⟨2057054723191761916628153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371369815461174611085435 2057054723191761916628153)
              ·
                refine ⟨1542791042393821437471115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057054723191761916628153 1542791042393821437471115)
                ·
                  refine ⟨2314186563590732156206673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542791042393821437471115 2314186563590732156206673)
                  ·
                    refine ⟨1735639922693049117155005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314186563590732156206673 1735639922693049117155005)
                    ·
                      refine ⟨650864971009893418933127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1735639922693049117155005 650864971009893418933127)
                      ·
                        rfl

theorem cell23_1267555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_1267555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267555 prefixEnd_1267555 := by exact prefixLift 1267555
  have htrace : WordTrace (prefixWord ++ tailWord_1267555) baseStart_1267555 baseEnd_1267555 := by
    simpa [prefixWord, tailWord_1267555, baseEnd_1267555] using wordTrace_append hprefix tailTrace_1267555
  have hstable : (prefixWord ++ tailWord_1267555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267555).length < 2 ^ (prefixWord ++ tailWord_1267555).sum := by decide
  have hdescent : baseEnd_1267555 < baseStart_1267555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267578 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2]
def baseStart_1267578 : Nat := 118140960795 + 1267578 * 2 ^ 59
def prefixEnd_1267578 : Nat := 4983230072969 + 3 ^ 40 * 1267578 * 2
def baseEnd_1267578 : Nat := 650876781064946828945521

theorem tailTrace_1267578 : CollatzResearch.WordTrace tailWord_1267578 prefixEnd_1267578 650876781064946828945521 := by
  unfold tailWord_1267578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558091950447216483062847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30821578534525910621500925 11558091950447216483062847)
  ·
    refine ⟨17337137925670824724594271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11558091950447216483062847 17337137925670824724594271)
    ·
      refine ⟨26005706888506237086891407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17337137925670824724594271 26005706888506237086891407)
      ·
        refine ⟨39008560332759355630337111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26005706888506237086891407 39008560332759355630337111)
        ·
          refine ⟨58512840499139033445505667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39008560332759355630337111 58512840499139033445505667)
          ·
            refine ⟨87769260748708550168258501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58512840499139033445505667 87769260748708550168258501)
            ·
              refine ⟨16456736390382853156548469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87769260748708550168258501 16456736390382853156548469)
              ·
                refine ⟨1542819036598392483426419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16456736390382853156548469 1542819036598392483426419)
                ·
                  refine ⟨2314228554897588725139629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542819036598392483426419 2314228554897588725139629)
                  ·
                    refine ⟨867835708086595771927361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2314228554897588725139629 867835708086595771927361)
                    ·
                      refine ⟨650876781064946828945521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 867835708086595771927361 650876781064946828945521)
                      ·
                        rfl

theorem cell23_1267578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_1267578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267578 prefixEnd_1267578 := by exact prefixLift 1267578
  have htrace : WordTrace (prefixWord ++ tailWord_1267578) baseStart_1267578 baseEnd_1267578 := by
    simpa [prefixWord, tailWord_1267578, baseEnd_1267578] using wordTrace_append hprefix tailTrace_1267578
  have hstable : (prefixWord ++ tailWord_1267578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267578).length < 2 ^ (prefixWord ++ tailWord_1267578).sum := by decide
  have hdescent : baseEnd_1267578 < baseStart_1267578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267584 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_1267584 : Nat := 118140960795 + 1267584 * 2 ^ 59
def prefixEnd_1267584 : Nat := 4983230072969 + 3 ^ 40 * 1267584 * 2
def baseEnd_1267584 : Nat := 216959953982957935156831

theorem tailTrace_1267584 : CollatzResearch.WordTrace tailWord_1267584 prefixEnd_1267584 216959953982957935156831 := by
  unfold tailWord_1267584
  simp only [CollatzResearch.WordTrace]
  refine ⟨23116293319883564478484903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30821724426511419304646537 23116293319883564478484903)
  ·
    refine ⟨34674439979825346717727355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23116293319883564478484903 34674439979825346717727355)
    ·
      refine ⟨52011659969738020076591033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34674439979825346717727355 52011659969738020076591033)
      ·
        refine ⟨39008744977303515057443275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52011659969738020076591033 39008744977303515057443275)
        ·
          refine ⟨58513117465955272586164913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39008744977303515057443275 58513117465955272586164913)
          ·
            refine ⟨43884838099466454439623685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58513117465955272586164913 43884838099466454439623685)
            ·
              refine ⟨8228407143649960207429441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43884838099466454439623685 8228407143649960207429441)
              ·
                refine ⟨6171305357737470155572081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8228407143649960207429441 6171305357737470155572081)
                ·
                  refine ⟨4628479018303102616679061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171305357737470155572081 4628479018303102616679061)
                  ·
                    refine ⟨216959953982957935156831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4628479018303102616679061 216959953982957935156831)
                    ·
                      rfl

theorem cell23_1267584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_1267584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267584 prefixEnd_1267584 := by exact prefixLift 1267584
  have htrace : WordTrace (prefixWord ++ tailWord_1267584) baseStart_1267584 baseEnd_1267584 := by
    simpa [prefixWord, tailWord_1267584, baseEnd_1267584] using wordTrace_append hprefix tailTrace_1267584
  have hstable : (prefixWord ++ tailWord_1267584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267584).length < 2 ^ (prefixWord ++ tailWord_1267584).sum := by decide
  have hdescent : baseEnd_1267584 < baseStart_1267584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267636 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1267636 : Nat := 118140960795 + 1267636 * 2 ^ 59
def prefixEnd_1267636 : Nat := 4983230072969 + 3 ^ 40 * 1267636 * 2
def baseEnd_1267636 : Nat := 650906562942907602020255

theorem tailTrace_1267636 : CollatzResearch.WordTrace tailWord_1267636 prefixEnd_1267636 650906562942907602020255 := by
  unfold tailWord_1267636
  simp only [CollatzResearch.WordTrace]
  refine ⟨23117241617789370918931381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30822988823719161225241841 23117241617789370918931381)
  ·
    refine ⟨2167241401667753523649817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23117241617789370918931381 2167241401667753523649817)
    ·
      refine ⟨1625431051250815142737363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2167241401667753523649817 1625431051250815142737363)
      ·
        refine ⟨2438146576876222714106045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625431051250815142737363 2438146576876222714106045)
        ·
          refine ⟨914304966328583517789767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2438146576876222714106045 914304966328583517789767)
          ·
            refine ⟨1371457449492875276684651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914304966328583517789767 1371457449492875276684651)
            ·
              refine ⟨2057186174239312915026977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371457449492875276684651 2057186174239312915026977)
              ·
                refine ⟨1542889630679484686270233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057186174239312915026977 1542889630679484686270233)
                ·
                  refine ⟨1157167223009613514702675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542889630679484686270233 1157167223009613514702675)
                  ·
                    refine ⟨1735750834514420272054013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1157167223009613514702675 1735750834514420272054013)
                    ·
                      refine ⟨650906562942907602020255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1735750834514420272054013 650906562942907602020255)
                      ·
                        rfl

theorem cell23_1267636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1267636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267636 prefixEnd_1267636 := by exact prefixLift 1267636
  have htrace : WordTrace (prefixWord ++ tailWord_1267636) baseStart_1267636 baseEnd_1267636 := by
    simpa [prefixWord, tailWord_1267636, baseEnd_1267636] using wordTrace_append hprefix tailTrace_1267636
  have hstable : (prefixWord ++ tailWord_1267636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267636).length < 2 ^ (prefixWord ++ tailWord_1267636).sum := by decide
  have hdescent : baseEnd_1267636 < baseStart_1267636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267641 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1267641 : Nat := 118140960795 + 1267641 * 2 ^ 59
def prefixEnd_1267641 : Nat := 4983230072969 + 3 ^ 40 * 1267641 * 2
def baseEnd_1267641 : Nat := 650909130346180082457731

theorem tailTrace_1267641 : CollatzResearch.WordTrace tailWord_1267641 prefixEnd_1267641 650909130346180082457731 := by
  unfold tailWord_1267641
  simp only [CollatzResearch.WordTrace]
  refine ⟨46234665600560627691794777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30823110400373751794529851 46234665600560627691794777)
  ·
    refine ⟨34675999200420470768846083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46234665600560627691794777 34675999200420470768846083)
    ·
      refine ⟨52013998800630706153269125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34675999200420470768846083 52013998800630706153269125)
      ·
        refine ⟨9752624775118257403737961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52013998800630706153269125 9752624775118257403737961)
        ·
          refine ⟨7314468581338693052803471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9752624775118257403737961 7314468581338693052803471)
          ·
            refine ⟨10971702872008039579205207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7314468581338693052803471 10971702872008039579205207)
            ·
              refine ⟨16457554308012059368807811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10971702872008039579205207 16457554308012059368807811)
              ·
                refine ⟨24686331462018089053211717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16457554308012059368807811 24686331462018089053211717)
                ·
                  refine ⟨4628687149128391697477197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24686331462018089053211717 4628687149128391697477197)
                  ·
                    refine ⟨1735757680923146886553949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4628687149128391697477197 1735757680923146886553949)
                    ·
                      refine ⟨650909130346180082457731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1735757680923146886553949 650909130346180082457731)
                      ·
                        rfl

theorem cell23_1267641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1267641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267641 prefixEnd_1267641 := by exact prefixLift 1267641
  have htrace : WordTrace (prefixWord ++ tailWord_1267641) baseStart_1267641 baseEnd_1267641 := by
    simpa [prefixWord, tailWord_1267641, baseEnd_1267641] using wordTrace_append hprefix tailTrace_1267641
  have hstable : (prefixWord ++ tailWord_1267641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267641).length < 2 ^ (prefixWord ++ tailWord_1267641).sum := by decide
  have hdescent : baseEnd_1267641 < baseStart_1267641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267681 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1267681 : Nat := 118140960795 + 1267681 * 2 ^ 59
def prefixEnd_1267681 : Nat := 4983230072969 + 3 ^ 40 * 1267681 * 2
def baseEnd_1267681 : Nat := 650929669572359925957547

theorem tailTrace_1267681 : CollatzResearch.WordTrace tailWord_1267681 prefixEnd_1267681 650929669572359925957547 := by
  unfold tailWord_1267681
  simp only [CollatzResearch.WordTrace]
  refine ⟨46236124520415714523250897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30824083013610476348833931 46236124520415714523250897)
  ·
    refine ⟨34677093390311785892438173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46236124520415714523250897 34677093390311785892438173)
    ·
      refine ⟨13003910021366919709664315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34677093390311785892438173 13003910021366919709664315)
      ·
        refine ⟨19505865032050379564496473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13003910021366919709664315 19505865032050379564496473)
        ·
          refine ⟨14629398774037784673372355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19505865032050379564496473 14629398774037784673372355)
          ·
            refine ⟨21944098161056677010058533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14629398774037784673372355 21944098161056677010058533)
            ·
              refine ⟨4114518405198126939385975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21944098161056677010058533 4114518405198126939385975)
              ·
                refine ⟨6171777607797190409078963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114518405198126939385975 6171777607797190409078963)
                ·
                  refine ⟨9257666411695785613618445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6171777607797190409078963 9257666411695785613618445)
                  ·
                    refine ⟨3471624904385919605106917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9257666411695785613618445 3471624904385919605106917)
                    ·
                      refine ⟨650929669572359925957547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3471624904385919605106917 650929669572359925957547)
                      ·
                        rfl

theorem cell23_1267681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1267681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267681 prefixEnd_1267681 := by exact prefixLift 1267681
  have htrace : WordTrace (prefixWord ++ tailWord_1267681) baseStart_1267681 baseEnd_1267681 := by
    simpa [prefixWord, tailWord_1267681, baseEnd_1267681] using wordTrace_append hprefix tailTrace_1267681
  have hstable : (prefixWord ++ tailWord_1267681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267681).length < 2 ^ (prefixWord ++ tailWord_1267681).sum := by decide
  have hdescent : baseEnd_1267681 < baseStart_1267681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267691 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 5, 4]
def baseStart_1267691 : Nat := 118140960795 + 1267691 * 2 ^ 59
def prefixEnd_1267691 : Nat := 4983230072969 + 3 ^ 40 * 1267691 * 2
def baseEnd_1267691 : Nat := 216978268126301628944167

theorem tailTrace_1267691 : CollatzResearch.WordTrace tailWord_1267691 prefixEnd_1267691 216978268126301628944167 := by
  unfold tailWord_1267691
  simp only [CollatzResearch.WordTrace]
  refine ⟨46236489250379486231114927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30824326166919657487409951 46236489250379486231114927)
  ·
    refine ⟨69354733875569229346672391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46236489250379486231114927 69354733875569229346672391)
    ·
      refine ⟨104032100813353844020008587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69354733875569229346672391 104032100813353844020008587)
      ·
        refine ⟨156048151220030766030012881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104032100813353844020008587 156048151220030766030012881)
        ·
          refine ⟨117036113415023074522509661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156048151220030766030012881 117036113415023074522509661)
          ·
            refine ⟨43888542530633652945941123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117036113415023074522509661 43888542530633652945941123)
            ·
              refine ⟨65832813795950479418911685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43888542530633652945941123 65832813795950479418911685)
              ·
                refine ⟨12343652586740714891045941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65832813795950479418911685 12343652586740714891045941)
                ·
                  refine ⟨1157217430006942021035557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12343652586740714891045941 1157217430006942021035557)
                  ·
                    refine ⟨216978268126301628944167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1157217430006942021035557 216978268126301628944167)
                    ·
                      rfl

theorem cell23_1267691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 4].length) (baseStart_1267691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267691 prefixEnd_1267691 := by exact prefixLift 1267691
  have htrace : WordTrace (prefixWord ++ tailWord_1267691) baseStart_1267691 baseEnd_1267691 := by
    simpa [prefixWord, tailWord_1267691, baseEnd_1267691] using wordTrace_append hprefix tailTrace_1267691
  have hstable : (prefixWord ++ tailWord_1267691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267691).length < 2 ^ (prefixWord ++ tailWord_1267691).sum := by decide
  have hdescent : baseEnd_1267691 < baseStart_1267691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267731 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 3]
def baseStart_1267731 : Nat := 118140960795 + 1267731 * 2 ^ 59
def prefixEnd_1267731 : Nat := 4983230072969 + 3 ^ 40 * 1267731 * 2
def baseEnd_1267731 : Nat := 650955343605084730332317

theorem tailTrace_1267731 : CollatzResearch.WordTrace tailWord_1267731 prefixEnd_1267731 650955343605084730332317 := by
  unfold tailWord_1267731
  simp only [CollatzResearch.WordTrace]
  refine ⟨46237948170234573062571047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30825298780156382041714031 46237948170234573062571047)
  ·
    refine ⟨69356922255351859593856571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46237948170234573062571047 69356922255351859593856571)
    ·
      refine ⟨104035383383027789390784857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69356922255351859593856571 104035383383027789390784857)
      ·
        refine ⟨78026537537270842043088643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104035383383027789390784857 78026537537270842043088643)
        ·
          refine ⟨117039806305906263064632965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78026537537270842043088643 117039806305906263064632965)
          ·
            refine ⟨21944963682357424324618681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117039806305906263064632965 21944963682357424324618681)
            ·
              refine ⟨16458722761768068243464011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21944963682357424324618681 16458722761768068243464011)
              ·
                refine ⟨24688084142652102365196017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16458722761768068243464011 24688084142652102365196017)
                ·
                  refine ⟨18516063106989076773897013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24688084142652102365196017 18516063106989076773897013)
                  ·
                    refine ⟨1735880916280225947552845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18516063106989076773897013 1735880916280225947552845)
                    ·
                      refine ⟨650955343605084730332317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1735880916280225947552845 650955343605084730332317)
                      ·
                        rfl

theorem cell23_1267731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_1267731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267731 prefixEnd_1267731 := by exact prefixLift 1267731
  have htrace : WordTrace (prefixWord ++ tailWord_1267731) baseStart_1267731 baseEnd_1267731 := by
    simpa [prefixWord, tailWord_1267731, baseEnd_1267731] using wordTrace_append hprefix tailTrace_1267731
  have hstable : (prefixWord ++ tailWord_1267731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267731).length < 2 ^ (prefixWord ++ tailWord_1267731).sum := by decide
  have hdescent : baseEnd_1267731 < baseStart_1267731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267788 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1267788 : Nat := 118140960795 + 1267788 * 2 ^ 59
def prefixEnd_1267788 : Nat := 4983230072969 + 3 ^ 40 * 1267788 * 2
def baseEnd_1267788 : Nat := 650984612002391007319555

theorem tailTrace_1267788 : CollatzResearch.WordTrace tailWord_1267788 prefixEnd_1267788 650984612002391007319555 := by
  unfold tailWord_1267788
  simp only [CollatzResearch.WordTrace]
  refine ⟨23120013565514035898698009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30826684754018714531597345 23120013565514035898698009)
  ·
    refine ⟨17340010174135526924023507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23120013565514035898698009 17340010174135526924023507)
    ·
      refine ⟨26010015261203290386035261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17340010174135526924023507 26010015261203290386035261)
      ·
        refine ⟨9753755722951233894763223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26010015261203290386035261 9753755722951233894763223)
        ·
          refine ⟨14630633584426850842144835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9753755722951233894763223 14630633584426850842144835)
          ·
            refine ⟨21945950376640276263217253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14630633584426850842144835 21945950376640276263217253)
            ·
              refine ⟨4114865695620051799353235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21945950376640276263217253 4114865695620051799353235)
              ·
                refine ⟨6172298543430077699029853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114865695620051799353235 6172298543430077699029853)
                ·
                  refine ⟨2314611953786279137136195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6172298543430077699029853 2314611953786279137136195)
                  ·
                    refine ⟨3471917930679418705704293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2314611953786279137136195 3471917930679418705704293)
                    ·
                      refine ⟨650984612002391007319555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3471917930679418705704293 650984612002391007319555)
                      ·
                        rfl

theorem cell23_1267788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1267788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267788 prefixEnd_1267788 := by exact prefixLift 1267788
  have htrace : WordTrace (prefixWord ++ tailWord_1267788) baseStart_1267788 baseEnd_1267788 := by
    simpa [prefixWord, tailWord_1267788, baseEnd_1267788] using wordTrace_append hprefix tailTrace_1267788
  have hstable : (prefixWord ++ tailWord_1267788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267788).length < 2 ^ (prefixWord ++ tailWord_1267788).sum := by decide
  have hdescent : baseEnd_1267788 < baseStart_1267788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267791 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_1267791 : Nat := 118140960795 + 1267791 * 2 ^ 59
def prefixEnd_1267791 : Nat := 4983230072969 + 3 ^ 40 * 1267791 * 2
def baseEnd_1267791 : Nat := 650986152444354495582041

theorem tailTrace_1267791 : CollatzResearch.WordTrace tailWord_1267791 prefixEnd_1267791 650986152444354495582041 := by
  unfold tailWord_1267791
  simp only [CollatzResearch.WordTrace]
  refine ⟨46240136550017203309755227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30826757700011468873170151 46240136550017203309755227)
  ·
    refine ⟨69360204825025804964632841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46240136550017203309755227 69360204825025804964632841)
    ·
      refine ⟨52020153618769353723474631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69360204825025804964632841 52020153618769353723474631)
      ·
        refine ⟨78030230428154030585211947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52020153618769353723474631 78030230428154030585211947)
        ·
          refine ⟨117045345642231045877817921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78030230428154030585211947 117045345642231045877817921)
          ·
            refine ⟨87784009231673284408363441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117045345642231045877817921 87784009231673284408363441)
            ·
              refine ⟨65838006923754963306272581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87784009231673284408363441 65838006923754963306272581)
              ·
                refine ⟨12344626298204055619926109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65838006923754963306272581 12344626298204055619926109)
                ·
                  refine ⟨4629234861826520857472291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12344626298204055619926109 4629234861826520857472291)
                  ·
                    refine ⟨6943852292739781286208437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4629234861826520857472291 6943852292739781286208437)
                    ·
                      refine ⟨650986152444354495582041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6943852292739781286208437 650986152444354495582041)
                      ·
                        rfl

theorem cell23_1267791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_1267791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267791 prefixEnd_1267791 := by exact prefixLift 1267791
  have htrace : WordTrace (prefixWord ++ tailWord_1267791) baseStart_1267791 baseEnd_1267791 := by
    simpa [prefixWord, tailWord_1267791, baseEnd_1267791] using wordTrace_append hprefix tailTrace_1267791
  have hstable : (prefixWord ++ tailWord_1267791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267791).length < 2 ^ (prefixWord ++ tailWord_1267791).sum := by decide
  have hdescent : baseEnd_1267791 < baseStart_1267791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267806 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1267806 : Nat := 118140960795 + 1267806 * 2 ^ 59
def prefixEnd_1267806 : Nat := 4983230072969 + 3 ^ 40 * 1267806 * 2
def baseEnd_1267806 : Nat := 72332650517130215210497

theorem tailTrace_1267806 : CollatzResearch.WordTrace tailWord_1267806 prefixEnd_1267806 72332650517130215210497 := by
  unfold tailWord_1267806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780085455620357608943909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30827122429975240581034181 5780085455620357608943909)
  ·
    refine ⟨1083766022928817051676983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5780085455620357608943909 1083766022928817051676983)
    ·
      refine ⟨1625649034393225577515475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083766022928817051676983 1625649034393225577515475)
      ·
        refine ⟨2438473551589838366273213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625649034393225577515475 2438473551589838366273213)
        ·
          refine ⟨914427581846189387352455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2438473551589838366273213 914427581846189387352455)
          ·
            refine ⟨1371641372769284081028683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914427581846189387352455 1371641372769284081028683)
            ·
              refine ⟨2057462059153926121543025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1371641372769284081028683 2057462059153926121543025)
              ·
                refine ⟨1543096544365444591157269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057462059153926121543025 1543096544365444591157269)
                ·
                  refine ⟨72332650517130215210497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1543096544365444591157269 72332650517130215210497)
                  ·
                    rfl

theorem cell23_1267806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1267806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267806 prefixEnd_1267806 := by exact prefixLift 1267806
  have htrace : WordTrace (prefixWord ++ tailWord_1267806) baseStart_1267806 baseEnd_1267806 := by
    simpa [prefixWord, tailWord_1267806, baseEnd_1267806] using wordTrace_append hprefix tailTrace_1267806
  have hstable : (prefixWord ++ tailWord_1267806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267806).length < 2 ^ (prefixWord ++ tailWord_1267806).sum := by decide
  have hdescent : baseEnd_1267806 < baseStart_1267806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267845 : List Nat := [1, 3, 1, 1, 5, 3, 2, 7]
def baseStart_1267845 : Nat := 118140960795 + 1267845 * 2 ^ 59
def prefixEnd_1267845 : Nat := 4983230072969 + 3 ^ 40 * 1267845 * 2
def baseEnd_1267845 : Nat := 24111625199988788307659

theorem tailTrace_1267845 : CollatzResearch.WordTrace tailWord_1267845 prefixEnd_1267845 24111625199988788307659 := by
  unfold tailWord_1267845
  simp only [CollatzResearch.WordTrace]
  refine ⟨46242106091821570532220989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30828070727881047021480659 46242106091821570532220989)
  ·
    refine ⟨17340789784433088949582871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46242106091821570532220989 17340789784433088949582871)
    ·
      refine ⟨26011184676649633424374307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17340789784433088949582871 26011184676649633424374307)
      ·
        refine ⟨39016777014974450136561461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26011184676649633424374307 39016777014974450136561461)
        ·
          refine ⟨3657822845153854700302637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39016777014974450136561461 3657822845153854700302637)
          ·
            refine ⟨1371683566932695512613489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3657822845153854700302637 1371683566932695512613489)
            ·
              refine ⟨1028762675199521634460117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371683566932695512613489 1028762675199521634460117)
              ·
                refine ⟨24111625199988788307659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1028762675199521634460117 24111625199988788307659)
                ·
                  rfl

theorem cell23_1267845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 7].length) (baseStart_1267845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267845 prefixEnd_1267845 := by exact prefixLift 1267845
  have htrace : WordTrace (prefixWord ++ tailWord_1267845) baseStart_1267845 baseEnd_1267845 := by
    simpa [prefixWord, tailWord_1267845, baseEnd_1267845] using wordTrace_append hprefix tailTrace_1267845
  have hstable : (prefixWord ++ tailWord_1267845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267845).length < 2 ^ (prefixWord ++ tailWord_1267845).sum := by decide
  have hdescent : baseEnd_1267845 < baseStart_1267845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267868 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1267868 : Nat := 118140960795 + 1267868 * 2 ^ 59
def prefixEnd_1267868 : Nat := 4983230072969 + 3 ^ 40 * 1267868 * 2
def baseEnd_1267868 : Nat := 651025690454750694319187

theorem tailTrace_1267868 : CollatzResearch.WordTrace tailWord_1267868 prefixEnd_1267868 651025690454750694319187 := by
  unfold tailWord_1267868
  simp only [CollatzResearch.WordTrace]
  refine ⟨23121472485369122730154129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30828629980492163640205505 23121472485369122730154129)
  ·
    refine ⟨17341104364026842047615597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23121472485369122730154129 17341104364026842047615597)
    ·
      refine ⟨6502914136510065767855849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17341104364026842047615597 6502914136510065767855849)
      ·
        refine ⟨4877185602382549325891887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6502914136510065767855849 4877185602382549325891887)
        ·
          refine ⟨7315778403573823988837831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877185602382549325891887 7315778403573823988837831)
          ·
            refine ⟨10973667605360735983256747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7315778403573823988837831 10973667605360735983256747)
            ·
              refine ⟨16460501408041103974885121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10973667605360735983256747 16460501408041103974885121)
              ·
                refine ⟨12345376056030827981163841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16460501408041103974885121 12345376056030827981163841)
                ·
                  refine ⟨9259032042023120985872881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12345376056030827981163841 9259032042023120985872881)
                  ·
                    refine ⟨6944274031517340739404661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9259032042023120985872881 6944274031517340739404661)
                    ·
                      refine ⟨651025690454750694319187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6944274031517340739404661 651025690454750694319187)
                      ·
                        rfl

theorem cell23_1267868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1267868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267868 prefixEnd_1267868 := by exact prefixLift 1267868
  have htrace : WordTrace (prefixWord ++ tailWord_1267868) baseStart_1267868 baseEnd_1267868 := by
    simpa [prefixWord, tailWord_1267868, baseEnd_1267868] using wordTrace_append hprefix tailTrace_1267868
  have hstable : (prefixWord ++ tailWord_1267868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267868).length < 2 ^ (prefixWord ++ tailWord_1267868).sum := by decide
  have hdescent : baseEnd_1267868 < baseStart_1267868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267889 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1267889 : Nat := 118140960795 + 1267889 * 2 ^ 59
def prefixEnd_1267889 : Nat := 4983230072969 + 3 ^ 40 * 1267889 * 2
def baseEnd_1267889 : Nat := 651036473548495112156591

theorem tailTrace_1267889 : CollatzResearch.WordTrace tailWord_1267889 prefixEnd_1267889 651036473548495112156591 := by
  unfold tailWord_1267889
  simp only [CollatzResearch.WordTrace]
  refine ⟨46243710903662166046822721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30829140602441444031215147 46243710903662166046822721)
  ·
    refine ⟨34682783177746624535117041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46243710903662166046822721 34682783177746624535117041)
    ·
      refine ⟨26012087383309968401337781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34682783177746624535117041 26012087383309968401337781)
      ·
        refine ⟨2438633192185309537625417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26012087383309968401337781 2438633192185309537625417)
        ·
          refine ⟨1828974894138982153219063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2438633192185309537625417 1828974894138982153219063)
          ·
            refine ⟨2743462341208473229828595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828974894138982153219063 2743462341208473229828595)
            ·
              refine ⟨4115193511812709844742893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743462341208473229828595 4115193511812709844742893)
              ·
                refine ⟨1543197566929766191778585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4115193511812709844742893 1543197566929766191778585)
                ·
                  refine ⟨1157398175197324643833939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1543197566929766191778585 1157398175197324643833939)
                  ·
                    refine ⟨1736097262795986965750909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1157398175197324643833939 1736097262795986965750909)
                    ·
                      refine ⟨651036473548495112156591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1736097262795986965750909 651036473548495112156591)
                      ·
                        rfl

theorem cell23_1267889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1267889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267889 prefixEnd_1267889 := by exact prefixLift 1267889
  have htrace : WordTrace (prefixWord ++ tailWord_1267889) baseStart_1267889 baseEnd_1267889 := by
    simpa [prefixWord, tailWord_1267889, baseEnd_1267889] using wordTrace_append hprefix tailTrace_1267889
  have hstable : (prefixWord ++ tailWord_1267889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267889).length < 2 ^ (prefixWord ++ tailWord_1267889).sum := by decide
  have hdescent : baseEnd_1267889 < baseStart_1267889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267898 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1267898 : Nat := 118140960795 + 1267898 * 2 ^ 59
def prefixEnd_1267898 : Nat := 4983230072969 + 3 ^ 40 * 1267898 * 2
def baseEnd_1267898 : Nat := 651041094874385576944049

theorem tailTrace_1267898 : CollatzResearch.WordTrace tailWord_1267898 prefixEnd_1267898 651041094874385576944049 := by
  unfold tailWord_1267898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561009790157390145975087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30829359440419707055933565 11561009790157390145975087)
  ·
    refine ⟨17341514685236085218962631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11561009790157390145975087 17341514685236085218962631)
    ·
      refine ⟨26012272027854127828443947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17341514685236085218962631 26012272027854127828443947)
      ·
        refine ⟨39018408041781191742665921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26012272027854127828443947 39018408041781191742665921)
        ·
          refine ⟨29263806031335893806999441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39018408041781191742665921 29263806031335893806999441)
          ·
            refine ⟨21947854523501920355249581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29263806031335893806999441 21947854523501920355249581)
            ·
              refine ⟨8230445446313220133218593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21947854523501920355249581 8230445446313220133218593)
              ·
                refine ⟨6172834084734915099913945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8230445446313220133218593 6172834084734915099913945)
                ·
                  refine ⟨4629625563551186324935459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6172834084734915099913945 4629625563551186324935459)
                  ·
                    refine ⟨6944438345326779487403189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4629625563551186324935459 6944438345326779487403189)
                    ·
                      refine ⟨651041094874385576944049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6944438345326779487403189 651041094874385576944049)
                      ·
                        rfl

theorem cell23_1267898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1267898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267898 prefixEnd_1267898 := by exact prefixLift 1267898
  have htrace : WordTrace (prefixWord ++ tailWord_1267898) baseStart_1267898 baseEnd_1267898 := by
    simpa [prefixWord, tailWord_1267898, baseEnd_1267898] using wordTrace_append hprefix tailTrace_1267898
  have hstable : (prefixWord ++ tailWord_1267898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267898).length < 2 ^ (prefixWord ++ tailWord_1267898).sum := by decide
  have hdescent : baseEnd_1267898 < baseStart_1267898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267948 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1267948 : Nat := 118140960795 + 1267948 * 2 ^ 59
def prefixEnd_1267948 : Nat := 4983230072969 + 3 ^ 40 * 1267948 * 2
def baseEnd_1267948 : Nat := 217022256302370127106273

theorem tailTrace_1267948 : CollatzResearch.WordTrace tailWord_1267948 prefixEnd_1267948 217022256302370127106273 := by
  unfold tailWord_1267948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23122931405224209561610249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30830575206965612748813665 23122931405224209561610249)
  ·
    refine ⟨17342198553918157171207687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23122931405224209561610249 17342198553918157171207687)
    ·
      refine ⟨26013297830877235756811531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17342198553918157171207687 26013297830877235756811531)
      ·
        refine ⟨39019946746315853635217297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26013297830877235756811531 39019946746315853635217297)
        ·
          refine ⟨29264960059736890226412973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39019946746315853635217297 29264960059736890226412973)
          ·
            refine ⟨10974360022401333834904865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29264960059736890226412973 10974360022401333834904865)
            ·
              refine ⟨8230770016801000376178649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10974360022401333834904865 8230770016801000376178649)
              ·
                refine ⟨6173077512600750282133987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8230770016801000376178649 6173077512600750282133987)
                ·
                  refine ⟨9259616268901125423200981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6173077512600750282133987 9259616268901125423200981)
                  ·
                    refine ⟨217022256302370127106273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9259616268901125423200981 217022256302370127106273)
                    ·
                      rfl

theorem cell23_1267948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1267948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267948 prefixEnd_1267948 := by exact prefixLift 1267948
  have htrace : WordTrace (prefixWord ++ tailWord_1267948) baseStart_1267948 baseEnd_1267948 := by
    simpa [prefixWord, tailWord_1267948, baseEnd_1267948] using wordTrace_append hprefix tailTrace_1267948
  have hstable : (prefixWord ++ tailWord_1267948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267948).length < 2 ^ (prefixWord ++ tailWord_1267948).sum := by decide
  have hdescent : baseEnd_1267948 < baseStart_1267948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267955 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 2, 5, 2]
def baseStart_1267955 : Nat := 118140960795 + 1267955 * 2 ^ 59
def prefixEnd_1267955 : Nat := 4983230072969 + 3 ^ 40 * 1267955 * 2
def baseEnd_1267955 : Nat := 651070363271691853931287

theorem tailTrace_1267955 : CollatzResearch.WordTrace tailWord_1267955 prefixEnd_1267955 651070363271691853931287 := by
  unfold tailWord_1267955
  simp only [CollatzResearch.WordTrace]
  refine ⟨46246118121423059318725319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30830745414282039545816879 46246118121423059318725319)
  ·
    refine ⟨69369177182134588978087979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46246118121423059318725319 69369177182134588978087979)
    ·
      refine ⟨104053765773201883467131969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69369177182134588978087979 104053765773201883467131969)
      ·
        refine ⟨78040324329901412600348977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104053765773201883467131969 78040324329901412600348977)
        ·
          refine ⟨58530243247426059450261733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78040324329901412600348977 58530243247426059450261733)
          ·
            refine ⟨10974420608892386146924075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58530243247426059450261733 10974420608892386146924075)
            ·
              refine ⟨16461630913338579220386113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10974420608892386146924075 16461630913338579220386113)
              ·
                refine ⟨12346223185003934415289585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16461630913338579220386113 12346223185003934415289585)
                ·
                  refine ⟨9259667388752950811467189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12346223185003934415289585 9259667388752950811467189)
                  ·
                    refine ⟨868093817695589138575049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9259667388752950811467189 868093817695589138575049)
                    ·
                      refine ⟨651070363271691853931287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868093817695589138575049 651070363271691853931287)
                      ·
                        rfl

theorem cell23_1267955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5, 2].length) (baseStart_1267955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267955 prefixEnd_1267955 := by exact prefixLift 1267955
  have htrace : WordTrace (prefixWord ++ tailWord_1267955) baseStart_1267955 baseEnd_1267955 := by
    simpa [prefixWord, tailWord_1267955, baseEnd_1267955] using wordTrace_append hprefix tailTrace_1267955
  have hstable : (prefixWord ++ tailWord_1267955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267955).length < 2 ^ (prefixWord ++ tailWord_1267955).sum := by decide
  have hdescent : baseEnd_1267955 < baseStart_1267955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1267995 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 3, 4]
def baseStart_1267995 : Nat := 118140960795 + 1267995 * 2 ^ 59
def prefixEnd_1267995 : Nat := 4983230072969 + 3 ^ 40 * 1267995 * 2
def baseEnd_1267995 : Nat := 217030300832623899143701

theorem tailTrace_1267995 : CollatzResearch.WordTrace tailWord_1267995 prefixEnd_1267995 217030300832623899143701 := by
  unfold tailWord_1267995
  simp only [CollatzResearch.WordTrace]
  refine ⟨46247577041278146150181439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30831718027518764100120959 46247577041278146150181439)
  ·
    refine ⟨69371365561917219225272159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46247577041278146150181439 69371365561917219225272159)
    ·
      refine ⟨104057048342875828837908239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69371365561917219225272159 104057048342875828837908239)
      ·
        refine ⟨156085572514313743256862359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104057048342875828837908239 156085572514313743256862359)
        ·
          refine ⟨234128358771470614885293539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156085572514313743256862359 234128358771470614885293539)
          ·
            refine ⟨351192538157205922327940309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234128358771470614885293539 351192538157205922327940309)
            ·
              refine ⟨8231075113059513804561101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 351192538157205922327940309 8231075113059513804561101)
              ·
                refine ⟨3086653167397317676710413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8231075113059513804561101 3086653167397317676710413)
                ·
                  refine ⟨1157494937773994128766405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3086653167397317676710413 1157494937773994128766405)
                  ·
                    refine ⟨217030300832623899143701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1157494937773994128766405 217030300832623899143701)
                    ·
                      rfl

theorem cell23_1267995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 4].length) (baseStart_1267995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1267995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1267995 prefixEnd_1267995 := by exact prefixLift 1267995
  have htrace : WordTrace (prefixWord ++ tailWord_1267995) baseStart_1267995 baseEnd_1267995 := by
    simpa [prefixWord, tailWord_1267995, baseEnd_1267995] using wordTrace_append hprefix tailTrace_1267995
  have hstable : (prefixWord ++ tailWord_1267995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1267995).length < 2 ^ (prefixWord ++ tailWord_1267995).sum := by decide
  have hdescent : baseEnd_1267995 < baseStart_1267995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1267995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268025 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 8]
def baseStart_1268025 : Nat := 118140960795 + 1268025 * 2 ^ 59
def prefixEnd_1268025 : Nat := 4983230072969 + 3 ^ 40 * 1268025 * 2
def baseEnd_1268025 : Nat := 72345145213056286672885

theorem tailTrace_1268025 : CollatzResearch.WordTrace tailWord_1268025 prefixEnd_1268025 72345145213056286672885 := by
  unfold tailWord_1268025
  simp only [CollatzResearch.WordTrace]
  refine ⟨46248671231169461273773529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30832447487446307515849019 46248671231169461273773529)
  ·
    refine ⟨34686503423377095955330147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46248671231169461273773529 34686503423377095955330147)
    ·
      refine ⟨52029755135065643932995221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34686503423377095955330147 52029755135065643932995221)
      ·
        refine ⟨2438894771956202059359151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52029755135065643932995221 2438894771956202059359151)
        ·
          refine ⟨3658342157934303089038727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438894771956202059359151 3658342157934303089038727)
          ·
            refine ⟨5487513236901454633558091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658342157934303089038727 5487513236901454633558091)
            ·
              refine ⟨8231269855352181950337137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487513236901454633558091 8231269855352181950337137)
              ·
                refine ⟨6173452391514136462752853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8231269855352181950337137 6173452391514136462752853)
                ·
                  refine ⟨72345145213056286672885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6173452391514136462752853 72345145213056286672885)
                  ·
                    rfl

theorem cell23_1268025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_1268025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268025 prefixEnd_1268025 := by exact prefixLift 1268025
  have htrace : WordTrace (prefixWord ++ tailWord_1268025) baseStart_1268025 baseEnd_1268025 := by
    simpa [prefixWord, tailWord_1268025, baseEnd_1268025] using wordTrace_append hprefix tailTrace_1268025
  have hstable : (prefixWord ++ tailWord_1268025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268025).length < 2 ^ (prefixWord ++ tailWord_1268025).sum := by decide
  have hdescent : baseEnd_1268025 < baseStart_1268025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268055 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 3, 5]
def baseStart_1268055 : Nat := 118140960795 + 1268055 * 2 ^ 59
def prefixEnd_1268055 : Nat := 4983230072969 + 3 ^ 40 * 1268055 * 2
def baseEnd_1268055 : Nat := 217040570445713820893609

theorem tailTrace_1268055 : CollatzResearch.WordTrace tailWord_1268055 prefixEnd_1268055 217040570445713820893609 := by
  unfold tailWord_1268055
  simp only [CollatzResearch.WordTrace]
  refine ⟨46249765421060776397365619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30833176947373850931577079 46249765421060776397365619)
  ·
    refine ⟨69374648131591164596048429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46249765421060776397365619 69374648131591164596048429)
    ·
      refine ⟨26015493049346686723518161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69374648131591164596048429 26015493049346686723518161)
      ·
        refine ⟨19511619787010015042638621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26015493049346686723518161 19511619787010015042638621)
        ·
          refine ⟨7316857420128755640989483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19511619787010015042638621 7316857420128755640989483)
          ·
            refine ⟨10975286130193133461484225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7316857420128755640989483 10975286130193133461484225)
            ·
              refine ⟨8231464597644850096113169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10975286130193133461484225 8231464597644850096113169)
              ·
                refine ⟨6173598448233637572084877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8231464597644850096113169 6173598448233637572084877)
                ·
                  refine ⟨2315099418087614089531829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6173598448233637572084877 2315099418087614089531829)
                  ·
                    refine ⟨217040570445713820893609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2315099418087614089531829 217040570445713820893609)
                    ·
                      rfl

theorem cell23_1268055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_1268055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268055 prefixEnd_1268055 := by exact prefixLift 1268055
  have htrace : WordTrace (prefixWord ++ tailWord_1268055) baseStart_1268055 baseEnd_1268055 := by
    simpa [prefixWord, tailWord_1268055, baseEnd_1268055] using wordTrace_append hprefix tailTrace_1268055
  have hstable : (prefixWord ++ tailWord_1268055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268055).length < 2 ^ (prefixWord ++ tailWord_1268055).sum := by decide
  have hdescent : baseEnd_1268055 < baseStart_1268055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268072 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1268072 : Nat := 118140960795 + 1268072 * 2 ^ 59
def prefixEnd_1268072 : Nat := 4983230072969 + 3 ^ 40 * 1268072 * 2
def baseEnd_1268072 : Nat := 217043480169422632056083

theorem tailTrace_1268072 : CollatzResearch.WordTrace tailWord_1268072 prefixEnd_1268072 217043480169422632056083 := by
  unfold tailWord_1268072
  simp only [CollatzResearch.WordTrace]
  refine ⟨23125192730999594150367235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30833590307999458867156313 23125192730999594150367235)
  ·
    refine ⟨34687789096499391225550853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23125192730999594150367235 34687789096499391225550853)
    ·
      refine ⟨6503960455593635854790785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34687789096499391225550853 6503960455593635854790785)
      ·
        refine ⟨4877970341695226891093089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6503960455593635854790785 4877970341695226891093089)
        ·
          refine ⟨3658477756271420168319817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4877970341695226891093089 3658477756271420168319817)
          ·
            refine ⟨2743858317203565126239863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3658477756271420168319817 2743858317203565126239863)
            ·
              refine ⟨4115787475805347689359795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743858317203565126239863 4115787475805347689359795)
              ·
                refine ⟨6173681213708021534039693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115787475805347689359795 6173681213708021534039693)
                ·
                  refine ⟨2315130455140508075264885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6173681213708021534039693 2315130455140508075264885)
                  ·
                    refine ⟨217043480169422632056083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2315130455140508075264885 217043480169422632056083)
                    ·
                      rfl

theorem cell23_1268072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1268072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268072 prefixEnd_1268072 := by exact prefixLift 1268072
  have htrace : WordTrace (prefixWord ++ tailWord_1268072) baseStart_1268072 baseEnd_1268072 := by
    simpa [prefixWord, tailWord_1268072, baseEnd_1268072] using wordTrace_append hprefix tailTrace_1268072
  have hstable : (prefixWord ++ tailWord_1268072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268072).length < 2 ^ (prefixWord ++ tailWord_1268072).sum := by decide
  have hdescent : baseEnd_1268072 < baseStart_1268072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268075 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 4]
def baseStart_1268075 : Nat := 118140960795 + 1268075 * 2 ^ 59
def prefixEnd_1268075 : Nat := 4983230072969 + 3 ^ 40 * 1268075 * 2
def baseEnd_1268075 : Nat := 651131980950231384430735

theorem tailTrace_1268075 : CollatzResearch.WordTrace tailWord_1268075 prefixEnd_1268075 651131980950231384430735 := by
  unfold tailWord_1268075
  simp only [CollatzResearch.WordTrace]
  refine ⟨46250494880988319813093679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30833663253992213208729119 46250494880988319813093679)
  ·
    refine ⟨69375742321482479719640519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46250494880988319813093679 69375742321482479719640519)
    ·
      refine ⟨104063613482223719579460779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69375742321482479719640519 104063613482223719579460779)
      ·
        refine ⟨156095420223335579369191169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104063613482223719579460779 156095420223335579369191169)
        ·
          refine ⟨117071565167501684526893377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156095420223335579369191169 117071565167501684526893377)
          ·
            refine ⟨87803673875626263395170033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117071565167501684526893377 87803673875626263395170033)
            ·
              refine ⟨65852755406719697546377525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87803673875626263395170033 65852755406719697546377525)
              ·
                refine ⟨6173695819379971644972893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65852755406719697546377525 6173695819379971644972893)
                ·
                  refine ⟨2315135932267489366864835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6173695819379971644972893 2315135932267489366864835)
                  ·
                    refine ⟨3472703898401234050297253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2315135932267489366864835 3472703898401234050297253)
                    ·
                      refine ⟨651131980950231384430735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3472703898401234050297253 651131980950231384430735)
                      ·
                        rfl

theorem cell23_1268075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 4].length) (baseStart_1268075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268075 prefixEnd_1268075 := by exact prefixLift 1268075
  have htrace : WordTrace (prefixWord ++ tailWord_1268075) baseStart_1268075 baseEnd_1268075 := by
    simpa [prefixWord, tailWord_1268075, baseEnd_1268075] using wordTrace_append hprefix tailTrace_1268075
  have hstable : (prefixWord ++ tailWord_1268075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268075).length < 2 ^ (prefixWord ++ tailWord_1268075).sum := by decide
  have hdescent : baseEnd_1268075 < baseStart_1268075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268122 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1268122 : Nat := 118140960795 + 1268122 * 2 ^ 59
def prefixEnd_1268122 : Nat := 4983230072969 + 3 ^ 40 * 1268122 * 2
def baseEnd_1268122 : Nat := 651156114540992700543019

theorem tailTrace_1268122 : CollatzResearch.WordTrace tailWord_1268122 prefixEnd_1268122 651156114540992700543019 := by
  unfold tailWord_1268122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11563052277954511710013655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30834806074545364560036413 11563052277954511710013655)
  ·
    refine ⟨17344578416931767565020483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11563052277954511710013655 17344578416931767565020483)
    ·
      refine ⟨26016867625397651347530725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17344578416931767565020483 26016867625397651347530725)
      ·
        refine ⟨4878162679762059627662011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26016867625397651347530725 4878162679762059627662011)
        ·
          refine ⟨7317244019643089441493017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878162679762059627662011 7317244019643089441493017)
          ·
            refine ⟨5487933014732317081119763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7317244019643089441493017 5487933014732317081119763)
            ·
              refine ⟨8231899522098475621679645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487933014732317081119763 8231899522098475621679645)
              ·
                refine ⟨3086962320786928358129867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8231899522098475621679645 3086962320786928358129867)
                ·
                  refine ⟨4630443481180392537194801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086962320786928358129867 4630443481180392537194801)
                  ·
                    refine ⟨3472832610885294402896101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4630443481180392537194801 3472832610885294402896101)
                    ·
                      refine ⟨651156114540992700543019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3472832610885294402896101 651156114540992700543019)
                      ·
                        rfl

theorem cell23_1268122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1268122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268122 prefixEnd_1268122 := by exact prefixLift 1268122
  have htrace : WordTrace (prefixWord ++ tailWord_1268122) baseStart_1268122 baseEnd_1268122 := by
    simpa [prefixWord, tailWord_1268122, baseEnd_1268122] using wordTrace_append hprefix tailTrace_1268122
  have hstable : (prefixWord ++ tailWord_1268122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268122).length < 2 ^ (prefixWord ++ tailWord_1268122).sum := by decide
  have hdescent : baseEnd_1268122 < baseStart_1268122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268186 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2]
def baseStart_1268186 : Nat := 118140960795 + 1268186 * 2 ^ 59
def prefixEnd_1268186 : Nat := 4983230072969 + 3 ^ 40 * 1268186 * 2
def baseEnd_1268186 : Nat := 651188977302880450142725

theorem tailTrace_1268186 : CollatzResearch.WordTrace tailWord_1268186 prefixEnd_1268186 651188977302880450142725 := by
  unfold tailWord_1268186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11563635845896546442596103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30836362255724123846922941 11563635845896546442596103)
  ·
    refine ⟨17345453768844819663894155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11563635845896546442596103 17345453768844819663894155)
    ·
      refine ⟨26018180653267229495841233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17345453768844819663894155 26018180653267229495841233)
      ·
        refine ⟨19513635489950422121880925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26018180653267229495841233 19513635489950422121880925)
        ·
          refine ⟨7317613308731408295705347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19513635489950422121880925 7317613308731408295705347)
          ·
            refine ⟨10976419963097112443558021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317613308731408295705347 10976419963097112443558021)
            ·
              refine ⟨2058078743080708583167129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10976419963097112443558021 2058078743080708583167129)
              ·
                refine ⟨1543559057310531437375347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058078743080708583167129 1543559057310531437375347)
                ·
                  refine ⟨2315338585965797156063021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543559057310531437375347 2315338585965797156063021)
                  ·
                    refine ⟨868251969737173933523633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315338585965797156063021 868251969737173933523633)
                    ·
                      refine ⟨651188977302880450142725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868251969737173933523633 651188977302880450142725)
                      ·
                        rfl

theorem cell23_1268186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_1268186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268186 prefixEnd_1268186 := by exact prefixLift 1268186
  have htrace : WordTrace (prefixWord ++ tailWord_1268186) baseStart_1268186 baseEnd_1268186 := by
    simpa [prefixWord, tailWord_1268186, baseEnd_1268186] using wordTrace_append hprefix tailTrace_1268186
  have hstable : (prefixWord ++ tailWord_1268186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268186).length < 2 ^ (prefixWord ++ tailWord_1268186).sum := by decide
  have hdescent : baseEnd_1268186 < baseStart_1268186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268194 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1268194 : Nat := 118140960795 + 1268194 * 2 ^ 59
def prefixEnd_1268194 : Nat := 4983230072969 + 3 ^ 40 * 1268194 * 2
def baseEnd_1268194 : Nat := 651193085148116418842689

theorem tailTrace_1268194 : CollatzResearch.WordTrace tailWord_1268194 prefixEnd_1268194 651193085148116418842689 := by
  unfold tailWord_1268194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11563708791889300784168909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30836556778371468757783757 11563708791889300784168909)
  ·
    refine ⟨4336390796958487794063341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11563708791889300784168909 4336390796958487794063341)
    ·
      refine ⟨1626146548859432922773753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4336390796958487794063341 1626146548859432922773753)
      ·
        refine ⟨1219609911644574692080315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626146548859432922773753 1219609911644574692080315)
        ·
          refine ⟨1829414867466862038120473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219609911644574692080315 1829414867466862038120473)
          ·
            refine ⟨1372061150600146528590355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829414867466862038120473 1372061150600146528590355)
            ·
              refine ⟨2058091725900219792885533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372061150600146528590355 2058091725900219792885533)
              ·
                refine ⟨771784397212582422332075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2058091725900219792885533 771784397212582422332075)
                ·
                  refine ⟨1157676595818873633498113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771784397212582422332075 1157676595818873633498113)
                  ·
                    refine ⟨868257446864155225123585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1157676595818873633498113 868257446864155225123585)
                    ·
                      refine ⟨651193085148116418842689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868257446864155225123585 651193085148116418842689)
                      ·
                        rfl

theorem cell23_1268194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1268194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268194 prefixEnd_1268194 := by exact prefixLift 1268194
  have htrace : WordTrace (prefixWord ++ tailWord_1268194) baseStart_1268194 baseEnd_1268194 := by
    simpa [prefixWord, tailWord_1268194, baseEnd_1268194] using wordTrace_append hprefix tailTrace_1268194
  have hstable : (prefixWord ++ tailWord_1268194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268194).length < 2 ^ (prefixWord ++ tailWord_1268194).sum := by decide
  have hdescent : baseEnd_1268194 < baseStart_1268194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268199 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1268199 : Nat := 118140960795 + 1268199 * 2 ^ 59
def prefixEnd_1268199 : Nat := 4983230072969 + 3 ^ 40 * 1268199 * 2
def baseEnd_1268199 : Nat := 651195652551388899280165

theorem tailTrace_1268199 : CollatzResearch.WordTrace tailWord_1268199 prefixEnd_1268199 651195652551388899280165 := by
  unfold tailWord_1268199
  simp only [CollatzResearch.WordTrace]
  refine ⟨46255017532539088990607651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30836678355026059327071767 46255017532539088990607651)
  ·
    refine ⟨69382526298808633485911477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46255017532539088990607651 69382526298808633485911477)
    ·
      refine ⟨6504611840513309389304201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69382526298808633485911477 6504611840513309389304201)
      ·
        refine ⟨4878458880384982041978151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6504611840513309389304201 4878458880384982041978151)
        ·
          refine ⟨7317688320577473062967227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878458880384982041978151 7317688320577473062967227)
          ·
            refine ⟨10976532480866209594450841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317688320577473062967227 10976532480866209594450841)
            ·
              refine ⟨8232399360649657195838131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976532480866209594450841 8232399360649657195838131)
              ·
                refine ⟨12348599040974485793757197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232399360649657195838131 12348599040974485793757197)
                ·
                  refine ⟨4630724640365432172658949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12348599040974485793757197 4630724640365432172658949)
                  ·
                    refine ⟨868260870068518532373553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4630724640365432172658949 868260870068518532373553)
                    ·
                      refine ⟨651195652551388899280165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868260870068518532373553 651195652551388899280165)
                      ·
                        rfl

theorem cell23_1268199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1268199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268199 prefixEnd_1268199 := by exact prefixLift 1268199
  have htrace : WordTrace (prefixWord ++ tailWord_1268199) baseStart_1268199 baseEnd_1268199 := by
    simpa [prefixWord, tailWord_1268199, baseEnd_1268199] using wordTrace_append hprefix tailTrace_1268199
  have hstable : (prefixWord ++ tailWord_1268199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268199).length < 2 ^ (prefixWord ++ tailWord_1268199).sum := by decide
  have hdescent : baseEnd_1268199 < baseStart_1268199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268202 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1268202 : Nat := 118140960795 + 1268202 * 2 ^ 59
def prefixEnd_1268202 : Nat := 4983230072969 + 3 ^ 40 * 1268202 * 2
def baseEnd_1268202 : Nat := 651197192993352387542651

theorem tailTrace_1268202 : CollatzResearch.WordTrace tailWord_1268202 prefixEnd_1268202 651197192993352387542651 := by
  unfold tailWord_1268202
  simp only [CollatzResearch.WordTrace]
  refine ⟨11563781737882055125741715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30836751301018813668644573 11563781737882055125741715)
  ·
    refine ⟨17345672606823082688612573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11563781737882055125741715 17345672606823082688612573)
    ·
      refine ⟨6504627227558656008229715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17345672606823082688612573 6504627227558656008229715)
      ·
        refine ⟨9756940841337984012344573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504627227558656008229715 9756940841337984012344573)
        ·
          refine ⟨3658852815501744004629215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9756940841337984012344573 3658852815501744004629215)
          ·
            refine ⟨5488279223252616006943823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658852815501744004629215 5488279223252616006943823)
            ·
              refine ⟨8232418834878924010415735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5488279223252616006943823 8232418834878924010415735)
              ·
                refine ⟨12348628252318386015623603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232418834878924010415735 12348628252318386015623603)
                ·
                  refine ⟨18522942378477579023435405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12348628252318386015623603 18522942378477579023435405)
                  ·
                    refine ⟨6946103391929092133788277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18522942378477579023435405 6946103391929092133788277)
                    ·
                      refine ⟨651197192993352387542651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6946103391929092133788277 651197192993352387542651)
                      ·
                        rfl

theorem cell23_1268202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1268202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268202 prefixEnd_1268202 := by exact prefixLift 1268202
  have htrace : WordTrace (prefixWord ++ tailWord_1268202) baseStart_1268202 baseEnd_1268202 := by
    simpa [prefixWord, tailWord_1268202, baseEnd_1268202] using wordTrace_append hprefix tailTrace_1268202
  have hstable : (prefixWord ++ tailWord_1268202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268202).length < 2 ^ (prefixWord ++ tailWord_1268202).sum := by decide
  have hdescent : baseEnd_1268202 < baseStart_1268202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268216 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 2, 2, 2]
def baseStart_1268216 : Nat := 118140960795 + 1268216 * 2 ^ 59
def prefixEnd_1268216 : Nat := 4983230072969 + 3 ^ 40 * 1268216 * 2
def baseEnd_1268216 : Nat := 651204381722515332767587

theorem tailTrace_1268216 : CollatzResearch.WordTrace tailWord_1268216 prefixEnd_1268216 651204381722515332767587 := by
  unfold tailWord_1268216
  simp only [CollatzResearch.WordTrace]
  refine ⟨23127818786738750446988251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30837091715651667262651001 23127818786738750446988251)
  ·
    refine ⟨34691728180108125670482377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23127818786738750446988251 34691728180108125670482377)
    ·
      refine ⟨26018796135081094252861783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34691728180108125670482377 26018796135081094252861783)
      ·
        refine ⟨39028194202621641379292675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26018796135081094252861783 39028194202621641379292675)
        ·
          refine ⟨58542291303932462068939013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39028194202621641379292675 58542291303932462068939013)
          ·
            refine ⟨10976679619487336637926065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58542291303932462068939013 10976679619487336637926065)
            ·
              refine ⟨8232509714615502478444549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976679619487336637926065 8232509714615502478444549)
              ·
                refine ⟨1543595571490406714708353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8232509714615502478444549 1543595571490406714708353)
                ·
                  refine ⟨1157696678617805036031265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1543595571490406714708353 1157696678617805036031265)
                  ·
                    refine ⟨868272508963353777023449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1157696678617805036031265 868272508963353777023449)
                    ·
                      refine ⟨651204381722515332767587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868272508963353777023449 651204381722515332767587)
                      ·
                        rfl

theorem cell23_1268216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_1268216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268216 prefixEnd_1268216 := by exact prefixLift 1268216
  have htrace : WordTrace (prefixWord ++ tailWord_1268216) baseStart_1268216 baseEnd_1268216 := by
    simpa [prefixWord, tailWord_1268216, baseEnd_1268216] using wordTrace_append hprefix tailTrace_1268216
  have hstable : (prefixWord ++ tailWord_1268216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268216).length < 2 ^ (prefixWord ++ tailWord_1268216).sum := by decide
  have hdescent : baseEnd_1268216 < baseStart_1268216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268232 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1268232 : Nat := 118140960795 + 1268232 * 2 ^ 59
def prefixEnd_1268232 : Nat := 4983230072969 + 3 ^ 40 * 1268232 * 2
def baseEnd_1268232 : Nat := 651212597412987270167513

theorem tailTrace_1268232 : CollatzResearch.WordTrace tailWord_1268232 prefixEnd_1268232 651212597412987270167513 := by
  unfold tailWord_1268232
  simp only [CollatzResearch.WordTrace]
  refine ⟨23128110570709767813279475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30837480760946357084372633 23128110570709767813279475)
  ·
    refine ⟨34692165856064651719919213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23128110570709767813279475 34692165856064651719919213)
    ·
      refine ⟨13009562196024244394969705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34692165856064651719919213 13009562196024244394969705)
      ·
        refine ⟨9757171647018183296227279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13009562196024244394969705 9757171647018183296227279)
        ·
          refine ⟨14635757470527274944340919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9757171647018183296227279 14635757470527274944340919)
          ·
            refine ⟨21953636205790912416511379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635757470527274944340919 21953636205790912416511379)
            ·
              refine ⟨32930454308686368624767069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21953636205790912416511379 32930454308686368624767069)
              ·
                refine ⟨12348920365757388234287651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32930454308686368624767069 12348920365757388234287651)
                ·
                  refine ⟨18523380548636082351431477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12348920365757388234287651 18523380548636082351431477)
                  ·
                    refine ⟨1736566926434632720446701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18523380548636082351431477 1736566926434632720446701)
                    ·
                      refine ⟨651212597412987270167513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1736566926434632720446701 651212597412987270167513)
                      ·
                        rfl

theorem cell23_1268232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1268232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268232 prefixEnd_1268232 := by exact prefixLift 1268232
  have htrace : WordTrace (prefixWord ++ tailWord_1268232) baseStart_1268232 baseEnd_1268232 := by
    simpa [prefixWord, tailWord_1268232, baseEnd_1268232] using wordTrace_append hprefix tailTrace_1268232
  have hstable : (prefixWord ++ tailWord_1268232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268232).length < 2 ^ (prefixWord ++ tailWord_1268232).sum := by decide
  have hdescent : baseEnd_1268232 < baseStart_1268232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268237 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1268237 : Nat := 118140960795 + 1268237 * 2 ^ 59
def prefixEnd_1268237 : Nat := 4983230072969 + 3 ^ 40 * 1268237 * 2
def baseEnd_1268237 : Nat := 651215164816259750604991

theorem tailTrace_1268237 : CollatzResearch.WordTrace tailWord_1268237 prefixEnd_1268237 651215164816259750604991 := by
  unfold tailWord_1268237
  simp only [CollatzResearch.WordTrace]
  refine ⟨46256403506401421480490965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30837602337600947653660643 46256403506401421480490965)
  ·
    refine ⟨1084134457181283315949007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 46256403506401421480490965 1084134457181283315949007)
    ·
      refine ⟨1626201685771924973923511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084134457181283315949007 1626201685771924973923511)
      ·
        refine ⟨2439302528657887460885267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626201685771924973923511 2439302528657887460885267)
        ·
          refine ⟨3658953792986831191327901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439302528657887460885267 3658953792986831191327901)
          ·
            refine ⟨1372107672370061696747963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3658953792986831191327901 1372107672370061696747963)
            ·
              refine ⟨2058161508555092545121945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372107672370061696747963 2058161508555092545121945)
              ·
                refine ⟨1543621131416319408841459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058161508555092545121945 1543621131416319408841459)
                ·
                  refine ⟨2315431697124479113262189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543621131416319408841459 2315431697124479113262189)
                  ·
                    refine ⟨868286886421679667473321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315431697124479113262189 868286886421679667473321)
                    ·
                      refine ⟨651215164816259750604991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868286886421679667473321 651215164816259750604991)
                      ·
                        rfl

theorem cell23_1268237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1268237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268237 prefixEnd_1268237 := by exact prefixLift 1268237
  have htrace : WordTrace (prefixWord ++ tailWord_1268237) baseStart_1268237 baseEnd_1268237 := by
    simpa [prefixWord, tailWord_1268237, baseEnd_1268237] using wordTrace_append hprefix tailTrace_1268237
  have hstable : (prefixWord ++ tailWord_1268237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268237).length < 2 ^ (prefixWord ++ tailWord_1268237).sum := by decide
  have hdescent : baseEnd_1268237 < baseStart_1268237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268332 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_1268332 : Nat := 118140960795 + 1268332 * 2 ^ 59
def prefixEnd_1268332 : Nat := 4983230072969 + 3 ^ 40 * 1268332 * 2
def baseEnd_1268332 : Nat := 651263945478436878917053

theorem tailTrace_1268332 : CollatzResearch.WordTrace tailWord_1268332 prefixEnd_1268332 651263945478436878917053 := by
  unfold tailWord_1268332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23129934220528626352599625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30839912294038168470132833 23129934220528626352599625)
  ·
    refine ⟨17347450665396469764449719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23129934220528626352599625 17347450665396469764449719)
    ·
      refine ⟨26021175998094704646674579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17347450665396469764449719 26021175998094704646674579)
      ·
        refine ⟨39031763997142056970011869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26021175998094704646674579 39031763997142056970011869)
        ·
          refine ⟨14636911498928271363754451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39031763997142056970011869 14636911498928271363754451)
          ·
            refine ⟨21955367248392407045631677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14636911498928271363754451 21955367248392407045631677)
            ·
              refine ⟨8233262718147152642111879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21955367248392407045631677 8233262718147152642111879)
              ·
                refine ⟨12349894077220728963167819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8233262718147152642111879 12349894077220728963167819)
                ·
                  refine ⟨18524841115831093444751729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12349894077220728963167819 18524841115831093444751729)
                  ·
                    refine ⟨13893630836873320083563797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18524841115831093444751729 13893630836873320083563797)
                    ·
                      refine ⟨651263945478436878917053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13893630836873320083563797 651263945478436878917053)
                      ·
                        rfl

theorem cell23_1268332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_1268332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268332 prefixEnd_1268332 := by exact prefixLift 1268332
  have htrace : WordTrace (prefixWord ++ tailWord_1268332) baseStart_1268332 baseEnd_1268332 := by
    simpa [prefixWord, tailWord_1268332, baseEnd_1268332] using wordTrace_append hprefix tailTrace_1268332
  have hstable : (prefixWord ++ tailWord_1268332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268332).length < 2 ^ (prefixWord ++ tailWord_1268332).sum := by decide
  have hdescent : baseEnd_1268332 < baseStart_1268332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268333 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1268333 : Nat := 118140960795 + 1268333 * 2 ^ 59
def prefixEnd_1268333 : Nat := 4983230072969 + 3 ^ 40 * 1268333 * 2
def baseEnd_1268333 : Nat := 217088152986363791668183

theorem tailTrace_1268333 : CollatzResearch.WordTrace tailWord_1268333 prefixEnd_1268333 217088152986363791668183 := by
  unfold tailWord_1268333
  simp only [CollatzResearch.WordTrace]
  refine ⟨46259904914053629875985653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30839936609369086583990435 46259904914053629875985653)
  ·
    refine ⟨4336866085692527800873655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46259904914053629875985653 4336866085692527800873655)
    ·
      refine ⟨6505299128538791701310483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4336866085692527800873655 6505299128538791701310483)
      ·
        refine ⟨9757948692808187551965725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6505299128538791701310483 9757948692808187551965725)
        ·
          refine ⟨3659230759803070331987147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9757948692808187551965725 3659230759803070331987147)
          ·
            refine ⟨5488846139704605497980721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659230759803070331987147 5488846139704605497980721)
            ·
              refine ⟨4116634604778454123485541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5488846139704605497980721 4116634604778454123485541)
              ·
                refine ⟨771868988395960148153539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4116634604778454123485541 771868988395960148153539)
                ·
                  refine ⟨1157803482593940222230309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771868988395960148153539 1157803482593940222230309)
                  ·
                    refine ⟨217088152986363791668183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1157803482593940222230309 217088152986363791668183)
                    ·
                      rfl

theorem cell23_1268333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1268333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268333 prefixEnd_1268333 := by exact prefixLift 1268333
  have htrace : WordTrace (prefixWord ++ tailWord_1268333) baseStart_1268333 baseEnd_1268333 := by
    simpa [prefixWord, tailWord_1268333, baseEnd_1268333] using wordTrace_append hprefix tailTrace_1268333
  have hstable : (prefixWord ++ tailWord_1268333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268333).length < 2 ^ (prefixWord ++ tailWord_1268333).sum := by decide
  have hdescent : baseEnd_1268333 < baseStart_1268333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268366 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1268366 : Nat := 118140960795 + 1268366 * 2 ^ 59
def prefixEnd_1268366 : Nat := 4983230072969 + 3 ^ 40 * 1268366 * 2
def baseEnd_1268366 : Nat := 651281403820689745891897

theorem tailTrace_1268366 : CollatzResearch.WordTrace tailWord_1268366 prefixEnd_1268366 651281403820689745891897 := by
  unfold tailWord_1268366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782638565366759563992119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30840739015289384341291301 5782638565366759563992119)
  ·
    refine ⟨8673957848050139345988179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5782638565366759563992119 8673957848050139345988179)
    ·
      refine ⟨13010936772075209018982269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8673957848050139345988179 13010936772075209018982269)
      ·
        refine ⟨4879101289528203382118351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13010936772075209018982269 4879101289528203382118351)
        ·
          refine ⟨7318651934292305073177527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879101289528203382118351 7318651934292305073177527)
          ·
            refine ⟨10977977901438457609766291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318651934292305073177527 10977977901438457609766291)
            ·
              refine ⟨16466966852157686414649437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10977977901438457609766291 16466966852157686414649437)
              ·
                refine ⟨6175112569559132405493539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16466966852157686414649437 6175112569559132405493539)
                ·
                  refine ⟨9262668854338698608240309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6175112569559132405493539 9262668854338698608240309)
                  ·
                    refine ⟨868375205094252994522529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9262668854338698608240309 868375205094252994522529)
                    ·
                      refine ⟨651281403820689745891897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868375205094252994522529 651281403820689745891897)
                      ·
                        rfl

theorem cell23_1268366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1268366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268366 prefixEnd_1268366 := by exact prefixLift 1268366
  have htrace : WordTrace (prefixWord ++ tailWord_1268366) baseStart_1268366 baseEnd_1268366 := by
    simpa [prefixWord, tailWord_1268366, baseEnd_1268366] using wordTrace_append hprefix tailTrace_1268366
  have hstable : (prefixWord ++ tailWord_1268366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268366).length < 2 ^ (prefixWord ++ tailWord_1268366).sum := by decide
  have hdescent : baseEnd_1268366 < baseStart_1268366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268399 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_1268399 : Nat := 118140960795 + 1268399 * 2 ^ 59
def prefixEnd_1268399 : Nat := 4983230072969 + 3 ^ 40 * 1268399 * 2
def baseEnd_1268399 : Nat := 651298348682288116779245

theorem tailTrace_1268399 : CollatzResearch.WordTrace tailWord_1268399 prefixEnd_1268399 651298348682288116779245 := by
  unfold tailWord_1268399
  simp only [CollatzResearch.WordTrace]
  refine ⟨46262312131814523147888251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30841541421209682098592167 46262312131814523147888251)
  ·
    refine ⟨69393468197721784721832377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46262312131814523147888251 69393468197721784721832377)
    ·
      refine ⟨52045101148291338541374283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69393468197721784721832377 52045101148291338541374283)
      ·
        refine ⟨78067651722437007812061425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52045101148291338541374283 78067651722437007812061425)
        ·
          refine ⟨58550738791827755859046069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78067651722437007812061425 58550738791827755859046069)
          ·
            refine ⟨5489131761733852111785569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58550738791827755859046069 5489131761733852111785569)
            ·
              refine ⟨4116848821300389083839177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5489131761733852111785569 4116848821300389083839177)
              ·
                refine ⟨3087636615975291812879383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116848821300389083839177 3087636615975291812879383)
                ·
                  refine ⟨4631454923962937719319075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087636615975291812879383 4631454923962937719319075)
                  ·
                    refine ⟨6947182385944406578978613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4631454923962937719319075 6947182385944406578978613)
                    ·
                      refine ⟨651298348682288116779245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6947182385944406578978613 651298348682288116779245)
                      ·
                        rfl

theorem cell23_1268399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_1268399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268399 prefixEnd_1268399 := by exact prefixLift 1268399
  have htrace : WordTrace (prefixWord ++ tailWord_1268399) baseStart_1268399 baseEnd_1268399 := by
    simpa [prefixWord, tailWord_1268399, baseEnd_1268399] using wordTrace_append hprefix tailTrace_1268399
  have hstable : (prefixWord ++ tailWord_1268399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268399).length < 2 ^ (prefixWord ++ tailWord_1268399).sum := by decide
  have hdescent : baseEnd_1268399 < baseStart_1268399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268409 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1268409 : Nat := 118140960795 + 1268409 * 2 ^ 59
def prefixEnd_1268409 : Nat := 4983230072969 + 3 ^ 40 * 1268409 * 2
def baseEnd_1268409 : Nat := 651303483488833077654199

theorem tailTrace_1268409 : CollatzResearch.WordTrace tailWord_1268409 prefixEnd_1268409 651303483488833077654199 := by
  unfold tailWord_1268409
  simp only [CollatzResearch.WordTrace]
  refine ⟨46262676861778294855752281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30841784574518863237168187 46262676861778294855752281)
  ·
    refine ⟨34697007646333721141814211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46262676861778294855752281 34697007646333721141814211)
    ·
      refine ⟨52045511469500581712721317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34697007646333721141814211 52045511469500581712721317)
      ·
        refine ⟨9758533400531359071135247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52045511469500581712721317 9758533400531359071135247)
        ·
          refine ⟨14637800100797038606702871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758533400531359071135247 14637800100797038606702871)
          ·
            refine ⟨21956700151195557910054307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14637800100797038606702871 21956700151195557910054307)
            ·
              refine ⟨32935050226793336865081461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21956700151195557910054307 32935050226793336865081461)
              ·
                refine ⟨3087660958761875331101387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32935050226793336865081461 3087660958761875331101387)
                ·
                  refine ⟨4631491438142812996652081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087660958761875331101387 4631491438142812996652081)
                  ·
                    refine ⟨3473618578607109747489061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631491438142812996652081 3473618578607109747489061)
                    ·
                      refine ⟨651303483488833077654199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3473618578607109747489061 651303483488833077654199)
                      ·
                        rfl

theorem cell23_1268409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1268409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268409 prefixEnd_1268409 := by exact prefixLift 1268409
  have htrace : WordTrace (prefixWord ++ tailWord_1268409) baseStart_1268409 baseEnd_1268409 := by
    simpa [prefixWord, tailWord_1268409, baseEnd_1268409] using wordTrace_append hprefix tailTrace_1268409
  have hstable : (prefixWord ++ tailWord_1268409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268409).length < 2 ^ (prefixWord ++ tailWord_1268409).sum := by decide
  have hdescent : baseEnd_1268409 < baseStart_1268409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268413 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1268413 : Nat := 118140960795 + 1268413 * 2 ^ 59
def prefixEnd_1268413 : Nat := 4983230072969 + 3 ^ 40 * 1268413 * 2
def baseEnd_1268413 : Nat := 651305537411451062004181

theorem tailTrace_1268413 : CollatzResearch.WordTrace tailWord_1268413 prefixEnd_1268413 651305537411451062004181 := by
  unfold tailWord_1268413
  simp only [CollatzResearch.WordTrace]
  refine ⟨46262822753763803538897893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30841881835842535692598595 46262822753763803538897893)
  ·
    refine ⟨8674279266330713163543355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46262822753763803538897893 8674279266330713163543355)
    ·
      refine ⟨13011418899496069745315033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8674279266330713163543355 13011418899496069745315033)
      ·
        refine ⟨9758564174622052308986275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13011418899496069745315033 9758564174622052308986275)
        ·
          refine ⟨14637846261933078463479413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758564174622052308986275 14637846261933078463479413)
          ·
            refine ⟨1372298087056226105951195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14637846261933078463479413 1372298087056226105951195)
            ·
              refine ⟨2058447130584339158926793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372298087056226105951195 2058447130584339158926793)
              ·
                refine ⟨1543835347938254369195095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2058447130584339158926793 1543835347938254369195095)
                ·
                  refine ⟨2315753021907381553792643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543835347938254369195095 2315753021907381553792643)
                  ·
                    refine ⟨3473629532861072330688965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2315753021907381553792643 3473629532861072330688965)
                    ·
                      refine ⟨651305537411451062004181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3473629532861072330688965 651305537411451062004181)
                      ·
                        rfl

theorem cell23_1268413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1268413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268413 prefixEnd_1268413 := by exact prefixLift 1268413
  have htrace : WordTrace (prefixWord ++ tailWord_1268413) baseStart_1268413 baseEnd_1268413 := by
    simpa [prefixWord, tailWord_1268413, baseEnd_1268413] using wordTrace_append hprefix tailTrace_1268413
  have hstable : (prefixWord ++ tailWord_1268413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268413).length < 2 ^ (prefixWord ++ tailWord_1268413).sum := by decide
  have hdescent : baseEnd_1268413 < baseStart_1268413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268416 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_1268416 : Nat := 118140960795 + 1268416 * 2 ^ 59
def prefixEnd_1268416 : Nat := 4983230072969 + 3 ^ 40 * 1268416 * 2
def baseEnd_1268416 : Nat := 651307077853414550266667

theorem tailTrace_1268416 : CollatzResearch.WordTrace tailWord_1268416 prefixEnd_1268416 651307077853414550266667 := by
  unfold tailWord_1268416
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131466086376467525628551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30841954781835290034171401 23131466086376467525628551)
  ·
    refine ⟨34697199129564701288442827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23131466086376467525628551 34697199129564701288442827)
    ·
      refine ⟨52045798694347051932664241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34697199129564701288442827 52045798694347051932664241)
      ·
        refine ⟨39034349020760288949498181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52045798694347051932664241 39034349020760288949498181)
        ·
          refine ⟨7318940441392554178030909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39034349020760288949498181 7318940441392554178030909)
          ·
            refine ⟨2744602665522207816761591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7318940441392554178030909 2744602665522207816761591)
            ·
              refine ⟨4116903998283311725142387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744602665522207816761591 4116903998283311725142387)
              ·
                refine ⟨6175355997424967587713581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116903998283311725142387 6175355997424967587713581)
                ·
                  refine ⟨2315758499034362845392593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6175355997424967587713581 2315758499034362845392593)
                  ·
                    refine ⟨1736818874275772134044445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315758499034362845392593 1736818874275772134044445)
                    ·
                      refine ⟨651307077853414550266667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1736818874275772134044445 651307077853414550266667)
                      ·
                        rfl

theorem cell23_1268416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_1268416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268416 prefixEnd_1268416 := by exact prefixLift 1268416
  have htrace : WordTrace (prefixWord ++ tailWord_1268416) baseStart_1268416 baseEnd_1268416 := by
    simpa [prefixWord, tailWord_1268416, baseEnd_1268416] using wordTrace_append hprefix tailTrace_1268416
  have hstable : (prefixWord ++ tailWord_1268416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268416).length < 2 ^ (prefixWord ++ tailWord_1268416).sum := by decide
  have hdescent : baseEnd_1268416 < baseStart_1268416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268417 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1268417 : Nat := 118140960795 + 1268417 * 2 ^ 59
def prefixEnd_1268417 : Nat := 4983230072969 + 3 ^ 40 * 1268417 * 2
def baseEnd_1268417 : Nat := 651307591334069046354163

theorem tailTrace_1268417 : CollatzResearch.WordTrace tailWord_1268417 prefixEnd_1268417 651307591334069046354163 := by
  unfold tailWord_1268417
  simp only [CollatzResearch.WordTrace]
  refine ⟨46262968645749312222043505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30841979097166208148029003 46262968645749312222043505)
  ·
    refine ⟨34697226484311984166532629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46262968645749312222043505 34697226484311984166532629)
    ·
      refine ⟨1626432491452124257806217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34697226484311984166532629 1626432491452124257806217)
      ·
        refine ⟨1219824368589093193354663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626432491452124257806217 1219824368589093193354663)
        ·
          refine ⟨1829736552883639790031995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219824368589093193354663 1829736552883639790031995)
          ·
            refine ⟨2744604829325459685047993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829736552883639790031995 2744604829325459685047993)
            ·
              refine ⟨2058453621994094763785995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2744604829325459685047993 2058453621994094763785995)
              ·
                refine ⟨3087680432991142145678993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058453621994094763785995 3087680432991142145678993)
                ·
                  refine ⟨2315760324743356609259245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087680432991142145678993 2315760324743356609259245)
                  ·
                    refine ⟨868410121778758728472217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2315760324743356609259245 868410121778758728472217)
                    ·
                      refine ⟨651307591334069046354163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868410121778758728472217 651307591334069046354163)
                      ·
                        rfl

theorem cell23_1268417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1268417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268417 prefixEnd_1268417 := by exact prefixLift 1268417
  have htrace : WordTrace (prefixWord ++ tailWord_1268417) baseStart_1268417 baseEnd_1268417 := by
    simpa [prefixWord, tailWord_1268417, baseEnd_1268417] using wordTrace_append hprefix tailTrace_1268417
  have hstable : (prefixWord ++ tailWord_1268417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268417).length < 2 ^ (prefixWord ++ tailWord_1268417).sum := by decide
  have hdescent : baseEnd_1268417 < baseStart_1268417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268426 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1268426 : Nat := 118140960795 + 1268426 * 2 ^ 59
def prefixEnd_1268426 : Nat := 4983230072969 + 3 ^ 40 * 1268426 * 2
def baseEnd_1268426 : Nat := 651312212659959511141621

theorem tailTrace_1268426 : CollatzResearch.WordTrace tailWord_1268426 prefixEnd_1268426 651312212659959511141621 := by
  unfold tailWord_1268426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565824225679176689780283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30842197935144471172747421 11565824225679176689780283)
  ·
    refine ⟨17348736338518765034670425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11565824225679176689780283 17348736338518765034670425)
    ·
      refine ⟨13011552253889073776002819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17348736338518765034670425 13011552253889073776002819)
      ·
        refine ⟨19517328380833610664004229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13011552253889073776002819 19517328380833610664004229)
        ·
          refine ⟨3659499071406301999500793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19517328380833610664004229 3659499071406301999500793)
          ·
            refine ⟨2744624303554726499625595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3659499071406301999500793 2744624303554726499625595)
            ·
              refine ⟨4116936455332089749438393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744624303554726499625595 4116936455332089749438393)
              ·
                refine ⟨3087702341499067312078795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116936455332089749438393 3087702341499067312078795)
                ·
                  refine ⟨4631553512248600968118193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087702341499067312078795 4631553512248600968118193)
                  ·
                    refine ⟨3473665134186450726088645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631553512248600968118193 3473665134186450726088645)
                    ·
                      refine ⟨651312212659959511141621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3473665134186450726088645 651312212659959511141621)
                      ·
                        rfl

theorem cell23_1268426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1268426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268426 prefixEnd_1268426 := by exact prefixLift 1268426
  have htrace : WordTrace (prefixWord ++ tailWord_1268426) baseStart_1268426 baseEnd_1268426 := by
    simpa [prefixWord, tailWord_1268426, baseEnd_1268426] using wordTrace_append hprefix tailTrace_1268426
  have hstable : (prefixWord ++ tailWord_1268426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268426).length < 2 ^ (prefixWord ++ tailWord_1268426).sum := by decide
  have hdescent : baseEnd_1268426 < baseStart_1268426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268433 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 1, 2, 3]
def baseStart_1268433 : Nat := 118140960795 + 1268433 * 2 ^ 59
def prefixEnd_1268433 : Nat := 4983230072969 + 3 ^ 40 * 1268433 * 2
def baseEnd_1268433 : Nat := 651315807024540983754089

theorem tailTrace_1268433 : CollatzResearch.WordTrace tailWord_1268433 prefixEnd_1268433 651315807024540983754089 := by
  unfold tailWord_1268433
  simp only [CollatzResearch.WordTrace]
  refine ⟨46263552213691346954625953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30842368142460897969750635 46263552213691346954625953)
  ·
    refine ⟨34697664160268510215969465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46263552213691346954625953 34697664160268510215969465)
    ·
      refine ⟨26023248120201382661977099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34697664160268510215969465 26023248120201382661977099)
      ·
        refine ⟨39034872180302073992965649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26023248120201382661977099 39034872180302073992965649)
        ·
          refine ⟨29276154135226555494724237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39034872180302073992965649 29276154135226555494724237)
          ·
            refine ⟨10978557800709958310521589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29276154135226555494724237 10978557800709958310521589)
            ·
              refine ⟨1029239793816558591611399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10978557800709958310521589 1029239793816558591611399)
              ·
                refine ⟨1543859690724837887417099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029239793816558591611399 1543859690724837887417099)
                ·
                  refine ⟨2315789536087256831125649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543859690724837887417099 2315789536087256831125649)
                  ·
                    refine ⟨1736842152065442623344237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315789536087256831125649 1736842152065442623344237)
                    ·
                      refine ⟨651315807024540983754089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1736842152065442623344237 651315807024540983754089)
                      ·
                        rfl

theorem cell23_1268433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_1268433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268433 prefixEnd_1268433 := by exact prefixLift 1268433
  have htrace : WordTrace (prefixWord ++ tailWord_1268433) baseStart_1268433 baseEnd_1268433 := by
    simpa [prefixWord, tailWord_1268433, baseEnd_1268433] using wordTrace_append hprefix tailTrace_1268433
  have hstable : (prefixWord ++ tailWord_1268433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268433).length < 2 ^ (prefixWord ++ tailWord_1268433).sum := by decide
  have hdescent : baseEnd_1268433 < baseStart_1268433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268436 : List Nat := [2, 4, 1, 3, 3, 10]
def baseStart_1268436 : Nat := 118140960795 + 1268436 * 2 ^ 59
def prefixEnd_1268436 : Nat := 4983230072969 + 3 ^ 40 * 1268436 * 2
def baseEnd_1268436 : Nat := 2680318302331294123525

theorem tailTrace_1268436 : CollatzResearch.WordTrace tailWord_1268436 prefixEnd_1268436 2680318302331294123525 := by
  unfold tailWord_1268436
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131830816340239233492581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30842441088453652311323441 23131830816340239233492581)
  ·
    refine ⟨4337218278063794856279859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23131830816340239233492581 4337218278063794856279859)
    ·
      refine ⟨6505827417095692284419789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337218278063794856279859 6505827417095692284419789)
      ·
        refine ⟨2439685281410884606657421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6505827417095692284419789 2439685281410884606657421)
        ·
          refine ⟨914881980529081727496533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2439685281410884606657421 914881980529081727496533)
          ·
            refine ⟨2680318302331294123525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 914881980529081727496533 2680318302331294123525)
            ·
              rfl

theorem cell23_1268436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 10].length) (baseStart_1268436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268436 prefixEnd_1268436 := by exact prefixLift 1268436
  have htrace : WordTrace (prefixWord ++ tailWord_1268436) baseStart_1268436 baseEnd_1268436 := by
    simpa [prefixWord, tailWord_1268436, baseEnd_1268436] using wordTrace_append hprefix tailTrace_1268436
  have hstable : (prefixWord ++ tailWord_1268436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268436).length < 2 ^ (prefixWord ++ tailWord_1268436).sum := by decide
  have hdescent : baseEnd_1268436 < baseStart_1268436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268447 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 1, 2, 2]
def baseStart_1268447 : Nat := 118140960795 + 1268447 * 2 ^ 59
def prefixEnd_1268447 : Nat := 4983230072969 + 3 ^ 40 * 1268447 * 2
def baseEnd_1268447 : Nat := 651322995753703928979025

theorem tailTrace_1268447 : CollatzResearch.WordTrace tailWord_1268447 prefixEnd_1268447 651322995753703928979025 := by
  unfold tailWord_1268447
  simp only [CollatzResearch.WordTrace]
  refine ⟨46264062835640627345635595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30842708557093751563757063 46264062835640627345635595)
  ·
    refine ⟨69396094253460941018453393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46264062835640627345635595 69396094253460941018453393)
    ·
      refine ⟨52047070690095705763840045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69396094253460941018453393 52047070690095705763840045)
      ·
        refine ⟨19517651508785889661440017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52047070690095705763840045 19517651508785889661440017)
        ·
          refine ⟨14638238631589417246080013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19517651508785889661440017 14638238631589417246080013)
          ·
            refine ⟨5489339486846031467280005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14638238631589417246080013 5489339486846031467280005)
            ·
              refine ⟨1029251153783630900115001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5489339486846031467280005 1029251153783630900115001)
              ·
                refine ⟨771938365337723175086251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029251153783630900115001 771938365337723175086251)
                ·
                  refine ⟨1157907548006584762629377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771938365337723175086251 1157907548006584762629377)
                  ·
                    refine ⟨868430661004938571972033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1157907548006584762629377 868430661004938571972033)
                    ·
                      refine ⟨651322995753703928979025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868430661004938571972033 651322995753703928979025)
                      ·
                        rfl

theorem cell23_1268447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_1268447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268447 prefixEnd_1268447 := by exact prefixLift 1268447
  have htrace : WordTrace (prefixWord ++ tailWord_1268447) baseStart_1268447 baseEnd_1268447 := by
    simpa [prefixWord, tailWord_1268447, baseEnd_1268447] using wordTrace_append hprefix tailTrace_1268447
  have hstable : (prefixWord ++ tailWord_1268447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268447).length < 2 ^ (prefixWord ++ tailWord_1268447).sum := by decide
  have hdescent : baseEnd_1268447 < baseStart_1268447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268449 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1268449 : Nat := 118140960795 + 1268449 * 2 ^ 59
def prefixEnd_1268449 : Nat := 4983230072969 + 3 ^ 40 * 1268449 * 2
def baseEnd_1268449 : Nat := 217108007571670973718005

theorem tailTrace_1268449 : CollatzResearch.WordTrace tailWord_1268449 prefixEnd_1268449 217108007571670973718005 := by
  unfold tailWord_1268449
  simp only [CollatzResearch.WordTrace]
  refine ⟨46264135781633381687208401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30842757187755587791472267 46264135781633381687208401)
  ·
    refine ⟨34698101836225036265406301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46264135781633381687208401 34698101836225036265406301)
    ·
      refine ⟨13011788188584388599527363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34698101836225036265406301 13011788188584388599527363)
      ·
        refine ⟨19517682282876582899291045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13011788188584388599527363 19517682282876582899291045)
        ·
          refine ⟨3659565428039359293617071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19517682282876582899291045 3659565428039359293617071)
          ·
            refine ⟨5489348142059038940425607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659565428039359293617071 5489348142059038940425607)
            ·
              refine ⟨8234022213088558410638411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489348142059038940425607 8234022213088558410638411)
              ·
                refine ⟨12351033319632837615957617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8234022213088558410638411 12351033319632837615957617)
                ·
                  refine ⟨9263274989724628211968213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12351033319632837615957617 9263274989724628211968213)
                  ·
                    refine ⟨217108007571670973718005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9263274989724628211968213 217108007571670973718005)
                    ·
                      rfl

theorem cell23_1268449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1268449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268449 prefixEnd_1268449 := by exact prefixLift 1268449
  have htrace : WordTrace (prefixWord ++ tailWord_1268449) baseStart_1268449 baseEnd_1268449 := by
    simpa [prefixWord, tailWord_1268449, baseEnd_1268449] using wordTrace_append hprefix tailTrace_1268449
  have hstable : (prefixWord ++ tailWord_1268449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268449).length < 2 ^ (prefixWord ++ tailWord_1268449).sum := by decide
  have hdescent : baseEnd_1268449 < baseStart_1268449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268463 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 3]
def baseStart_1268463 : Nat := 118140960795 + 1268463 * 2 ^ 59
def prefixEnd_1268463 : Nat := 4983230072969 + 3 ^ 40 * 1268463 * 2
def baseEnd_1268463 : Nat := 651331211444175866378951

theorem tailTrace_1268463 : CollatzResearch.WordTrace tailWord_1268463 prefixEnd_1268463 651331211444175866378951 := by
  unfold tailWord_1268463
  simp only [CollatzResearch.WordTrace]
  refine ⟨46264646403582662078218043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30843097602388441385478695 46264646403582662078218043)
  ·
    refine ⟨69396969605373993117327065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46264646403582662078218043 69396969605373993117327065)
    ·
      refine ⟨52047727204030494837995299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69396969605373993117327065 52047727204030494837995299)
      ·
        refine ⟨78071590806045742256992949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52047727204030494837995299 78071590806045742256992949)
        ·
          refine ⟨7319211638066788336593089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78071590806045742256992949 7319211638066788336593089)
          ·
            refine ⟨5489408728550091252444817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7319211638066788336593089 5489408728550091252444817)
            ·
              refine ⟨4117056546412568439333613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5489408728550091252444817 4117056546412568439333613)
              ·
                refine ⟨1543896204904713164750105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4117056546412568439333613 1543896204904713164750105)
                ·
                  refine ⟨1157922153678534873562579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1543896204904713164750105 1157922153678534873562579)
                  ·
                    refine ⟨1736883230517802310343869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1157922153678534873562579 1736883230517802310343869)
                    ·
                      refine ⟨651331211444175866378951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1736883230517802310343869 651331211444175866378951)
                      ·
                        rfl

theorem cell23_1268463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 3].length) (baseStart_1268463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268463 prefixEnd_1268463 := by exact prefixLift 1268463
  have htrace : WordTrace (prefixWord ++ tailWord_1268463) baseStart_1268463 baseEnd_1268463 := by
    simpa [prefixWord, tailWord_1268463, baseEnd_1268463] using wordTrace_append hprefix tailTrace_1268463
  have hstable : (prefixWord ++ tailWord_1268463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268463).length < 2 ^ (prefixWord ++ tailWord_1268463).sum := by decide
  have hdescent : baseEnd_1268463 < baseStart_1268463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268489 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_1268489 : Nat := 118140960795 + 1268489 * 2 ^ 59
def prefixEnd_1268489 : Nat := 4983230072969 + 3 ^ 40 * 1268489 * 2
def baseEnd_1268489 : Nat := 651344561941192764653831

theorem tailTrace_1268489 : CollatzResearch.WordTrace tailWord_1268489 prefixEnd_1268489 651344561941192764653831 := by
  unfold tailWord_1268489
  simp only [CollatzResearch.WordTrace]
  refine ⟨46265594701488468518664521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30843729800992312345776347 46265594701488468518664521)
  ·
    refine ⟨34699196026116351388998391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46265594701488468518664521 34699196026116351388998391)
    ·
      refine ⟨52048794039174527083497587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34699196026116351388998391 52048794039174527083497587)
      ·
        refine ⟨78073191058761790625246381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52048794039174527083497587 78073191058761790625246381)
        ·
          refine ⟨29277446647035671484467393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78073191058761790625246381 29277446647035671484467393)
          ·
            refine ⟨21958084985276753613350545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29277446647035671484467393 21958084985276753613350545)
            ·
              refine ⟨16468563738957565210012909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21958084985276753613350545 16468563738957565210012909)
              ·
                refine ⟨6175711402109086953754841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16468563738957565210012909 6175711402109086953754841)
                ·
                  refine ⟨4631783551581815215316131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6175711402109086953754841 4631783551581815215316131)
                  ·
                    refine ⟨6947675327372722822974197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4631783551581815215316131 6947675327372722822974197)
                    ·
                      refine ⟨651344561941192764653831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6947675327372722822974197 651344561941192764653831)
                      ·
                        rfl

theorem cell23_1268489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_1268489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268489 prefixEnd_1268489 := by exact prefixLift 1268489
  have htrace : WordTrace (prefixWord ++ tailWord_1268489) baseStart_1268489 baseEnd_1268489 := by
    simpa [prefixWord, tailWord_1268489, baseEnd_1268489] using wordTrace_append hprefix tailTrace_1268489
  have hstable : (prefixWord ++ tailWord_1268489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268489).length < 2 ^ (prefixWord ++ tailWord_1268489).sum := by decide
  have hdescent : baseEnd_1268489 < baseStart_1268489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268499 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4]
def baseStart_1268499 : Nat := 118140960795 + 1268499 * 2 ^ 59
def prefixEnd_1268499 : Nat := 4983230072969 + 3 ^ 40 * 1268499 * 2
def baseEnd_1268499 : Nat := 651349696747737725528785

theorem tailTrace_1268499 : CollatzResearch.WordTrace tailWord_1268499 prefixEnd_1268499 651349696747737725528785 := by
  unfold tailWord_1268499
  simp only [CollatzResearch.WordTrace]
  refine ⟨46265959431452240226528551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30843972954301493484352367 46265959431452240226528551)
  ·
    refine ⟨69398939147178360339792827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46265959431452240226528551 69398939147178360339792827)
    ·
      refine ⟨104098408720767540509689241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69398939147178360339792827 104098408720767540509689241)
      ·
        refine ⟨78073806540575655382266931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104098408720767540509689241 78073806540575655382266931)
        ·
          refine ⟨117110709810863483073400397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78073806540575655382266931 117110709810863483073400397)
          ·
            refine ⟨43916516179073806152525149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117110709810863483073400397 43916516179073806152525149)
            ·
              refine ⟨16468693567152677307196931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43916516179073806152525149 16468693567152677307196931)
              ·
                refine ⟨24703040350729015960795397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16468693567152677307196931 24703040350729015960795397)
                ·
                  refine ⟨4631820065761690492649137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24703040350729015960795397 4631820065761690492649137)
                  ·
                    refine ⟨3473865049321267869486853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4631820065761690492649137 3473865049321267869486853)
                    ·
                      refine ⟨651349696747737725528785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3473865049321267869486853 651349696747737725528785)
                      ·
                        rfl

theorem cell23_1268499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_1268499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268499 prefixEnd_1268499 := by exact prefixLift 1268499
  have htrace : WordTrace (prefixWord ++ tailWord_1268499) baseStart_1268499 baseEnd_1268499 := by
    simpa [prefixWord, tailWord_1268499, baseEnd_1268499] using wordTrace_append hprefix tailTrace_1268499
  have hstable : (prefixWord ++ tailWord_1268499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268499).length < 2 ^ (prefixWord ++ tailWord_1268499).sum := by decide
  have hdescent : baseEnd_1268499 < baseStart_1268499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268543 : List Nat := [1, 1, 2, 2, 5, 1, 3, 3, 5]
def baseStart_1268543 : Nat := 118140960795 + 1268543 * 2 ^ 59
def prefixEnd_1268543 : Nat := 4983230072969 + 3 ^ 40 * 1268543 * 2
def baseEnd_1268543 : Nat := 72374698877392839264287

theorem tailTrace_1268543 : CollatzResearch.WordTrace tailWord_1268543 prefixEnd_1268543 72374698877392839264287 := by
  unfold tailWord_1268543
  simp only [CollatzResearch.WordTrace]
  refine ⟨46267564243292835741130283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30845042828861890494086855 46267564243292835741130283)
  ·
    refine ⟨69401346364939253611695425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46267564243292835741130283 69401346364939253611695425)
    ·
      refine ⟨52051009773704440208771569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69401346364939253611695425 52051009773704440208771569)
      ·
        refine ⟨39038257330278330156578677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52051009773704440208771569 39038257330278330156578677)
        ·
          refine ⟨3659836624713593452179251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39038257330278330156578677 3659836624713593452179251)
          ·
            refine ⟨5489754937070390178268877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659836624713593452179251 5489754937070390178268877)
            ·
              refine ⟨2058658101401396316850829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5489754937070390178268877 2058658101401396316850829)
              ·
                refine ⟨771996788025523618819061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2058658101401396316850829 771996788025523618819061)
                ·
                  refine ⟨72374698877392839264287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 771996788025523618819061 72374698877392839264287)
                  ·
                    rfl

theorem cell23_1268543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 5].length) (baseStart_1268543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268543 prefixEnd_1268543 := by exact prefixLift 1268543
  have htrace : WordTrace (prefixWord ++ tailWord_1268543) baseStart_1268543 baseEnd_1268543 := by
    simpa [prefixWord, tailWord_1268543, baseEnd_1268543] using wordTrace_append hprefix tailTrace_1268543
  have hstable : (prefixWord ++ tailWord_1268543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268543).length < 2 ^ (prefixWord ++ tailWord_1268543).sum := by decide
  have hdescent : baseEnd_1268543 < baseStart_1268543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268556 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_1268556 : Nat := 118140960795 + 1268556 * 2 ^ 59
def prefixEnd_1268556 : Nat := 4983230072969 + 3 ^ 40 * 1268556 * 2
def baseEnd_1268556 : Nat := 217126321715014667505341

theorem tailTrace_1268556 : CollatzResearch.WordTrace tailWord_1268556 prefixEnd_1268556 217126321715014667505341 := by
  unfold tailWord_1268556
  simp only [CollatzResearch.WordTrace]
  refine ⟨23134019196122869480676761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30845358928163825974235681 23134019196122869480676761)
  ·
    refine ⟨17350514397092152110507571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23134019196122869480676761 17350514397092152110507571)
    ·
      refine ⟨26025771595638228165761357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17350514397092152110507571 26025771595638228165761357)
      ·
        refine ⟨9759664348364335562160509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26025771595638228165761357 9759664348364335562160509)
        ·
          refine ⟨3659874130636625835810191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9759664348364335562160509 3659874130636625835810191)
          ·
            refine ⟨5489811195954938753715287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659874130636625835810191 5489811195954938753715287)
            ·
              refine ⟨8234716793932408130572931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489811195954938753715287 8234716793932408130572931)
              ·
                refine ⟨12352075190898612195859397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8234716793932408130572931 12352075190898612195859397)
                ·
                  refine ⟨2316014098293489786723637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12352075190898612195859397 2316014098293489786723637)
                  ·
                    refine ⟨217126321715014667505341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2316014098293489786723637 217126321715014667505341)
                    ·
                      rfl

theorem cell23_1268556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_1268556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268556 prefixEnd_1268556 := by exact prefixLift 1268556
  have htrace : WordTrace (prefixWord ++ tailWord_1268556) baseStart_1268556 baseEnd_1268556 := by
    simpa [prefixWord, tailWord_1268556, baseEnd_1268556] using wordTrace_append hprefix tailTrace_1268556
  have hstable : (prefixWord ++ tailWord_1268556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268556).length < 2 ^ (prefixWord ++ tailWord_1268556).sum := by decide
  have hdescent : baseEnd_1268556 < baseStart_1268556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268559 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_1268559 : Nat := 118140960795 + 1268559 * 2 ^ 59
def prefixEnd_1268559 : Nat := 4983230072969 + 3 ^ 40 * 1268559 * 2
def baseEnd_1268559 : Nat := 651380505587007490778509

theorem tailTrace_1268559 : CollatzResearch.WordTrace tailWord_1268559 prefixEnd_1268559 651380505587007490778509 := by
  unfold tailWord_1268559
  simp only [CollatzResearch.WordTrace]
  refine ⟨46268147811234870473712731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30845431874156580315808487 46268147811234870473712731)
  ·
    refine ⟨69402221716852305710569097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46268147811234870473712731 69402221716852305710569097)
    ·
      refine ⟨52051666287639229282926823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69402221716852305710569097 52051666287639229282926823)
      ·
        refine ⟨78077499431458843924390235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52051666287639229282926823 78077499431458843924390235)
        ·
          refine ⟨117116249147188265886585353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78077499431458843924390235 117116249147188265886585353)
          ·
            refine ⟨87837186860391199414939015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117116249147188265886585353 87837186860391199414939015)
            ·
              refine ⟨131755780290586799122408523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87837186860391199414939015 131755780290586799122408523)
              ·
                refine ⟨197633670435880198683612785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131755780290586799122408523 197633670435880198683612785)
                ·
                  refine ⟨148225252826910149012709589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197633670435880198683612785 148225252826910149012709589)
                  ·
                    refine ⟨3474029363130706617485381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148225252826910149012709589 3474029363130706617485381)
                    ·
                      refine ⟨651380505587007490778509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3474029363130706617485381 651380505587007490778509)
                      ·
                        rfl

theorem cell23_1268559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_1268559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268559 prefixEnd_1268559 := by exact prefixLift 1268559
  have htrace : WordTrace (prefixWord ++ tailWord_1268559) baseStart_1268559 baseEnd_1268559 := by
    simpa [prefixWord, tailWord_1268559, baseEnd_1268559] using wordTrace_append hprefix tailTrace_1268559
  have hstable : (prefixWord ++ tailWord_1268559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268559).length < 2 ^ (prefixWord ++ tailWord_1268559).sum := by decide
  have hdescent : baseEnd_1268559 < baseStart_1268559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268576 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1268576 : Nat := 118140960795 + 1268576 * 2 ^ 59
def prefixEnd_1268576 : Nat := 4983230072969 + 3 ^ 40 * 1268576 * 2
def baseEnd_1268576 : Nat := 651389234758133924265931

theorem tailTrace_1268576 : CollatzResearch.WordTrace tailWord_1268576 prefixEnd_1268576 651389234758133924265931 := by
  unfold tailWord_1268576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23134383926086641188540791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30845845234782188251387721 23134383926086641188540791)
  ·
    refine ⟨34701575889129961782811187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23134383926086641188540791 34701575889129961782811187)
    ·
      refine ⟨52052363833694942674216781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34701575889129961782811187 52052363833694942674216781)
      ·
        refine ⟨19519636437635603502831293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52052363833694942674216781 19519636437635603502831293)
        ·
          refine ⟨7319863664113351313561735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19519636437635603502831293 7319863664113351313561735)
          ·
            refine ⟨10979795496170026970342603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7319863664113351313561735 10979795496170026970342603)
            ·
              refine ⟨16469693244255040455513905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10979795496170026970342603 16469693244255040455513905)
              ·
                refine ⟨12352269933191280341635429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16469693244255040455513905 12352269933191280341635429)
                ·
                  refine ⟨2316050612473365064056643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12352269933191280341635429 2316050612473365064056643)
                  ·
                    refine ⟨3474075918710047596084965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2316050612473365064056643 3474075918710047596084965)
                    ·
                      refine ⟨651389234758133924265931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3474075918710047596084965 651389234758133924265931)
                      ·
                        rfl

theorem cell23_1268576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1268576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268576 prefixEnd_1268576 := by exact prefixLift 1268576
  have htrace : WordTrace (prefixWord ++ tailWord_1268576) baseStart_1268576 baseEnd_1268576 := by
    simpa [prefixWord, tailWord_1268576, baseEnd_1268576] using wordTrace_append hprefix tailTrace_1268576
  have hstable : (prefixWord ++ tailWord_1268576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268576).length < 2 ^ (prefixWord ++ tailWord_1268576).sum := by decide
  have hdescent : baseEnd_1268576 < baseStart_1268576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268590 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1268590 : Nat := 118140960795 + 1268590 * 2 ^ 59
def prefixEnd_1268590 : Nat := 4983230072969 + 3 ^ 40 * 1268590 * 2
def baseEnd_1268590 : Nat := 217132141162432289830289

theorem tailTrace_1268590 : CollatzResearch.WordTrace tailWord_1268590 prefixEnd_1268590 217132141162432289830289 := by
  unfold tailWord_1268590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5783659809265320346011403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30846185649415041845394149 5783659809265320346011403)
  ·
    refine ⟨8675489713897980519017105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5783659809265320346011403 8675489713897980519017105)
    ·
      refine ⟨6506617285423485389262829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8675489713897980519017105 6506617285423485389262829)
      ·
        refine ⟨2439981482033807020973561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6506617285423485389262829 2439981482033807020973561)
        ·
          refine ⟨1829986111525355265730171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439981482033807020973561 1829986111525355265730171)
          ·
            refine ⟨2744979167288032898595257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829986111525355265730171 2744979167288032898595257)
            ·
              refine ⟨2058734375466024673946443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2744979167288032898595257 2058734375466024673946443)
              ·
                refine ⟨3088101563199037010919665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058734375466024673946443 3088101563199037010919665)
                ·
                  refine ⟨2316076172399277758189749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3088101563199037010919665 2316076172399277758189749)
                  ·
                    refine ⟨217132141162432289830289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2316076172399277758189749 217132141162432289830289)
                    ·
                      rfl

theorem cell23_1268590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1268590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268590 prefixEnd_1268590 := by exact prefixLift 1268590
  have htrace : WordTrace (prefixWord ++ tailWord_1268590) baseStart_1268590 baseEnd_1268590 := by
    simpa [prefixWord, tailWord_1268590, baseEnd_1268590] using wordTrace_append hprefix tailTrace_1268590
  have hstable : (prefixWord ++ tailWord_1268590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268590).length < 2 ^ (prefixWord ++ tailWord_1268590).sum := by decide
  have hdescent : baseEnd_1268590 < baseStart_1268590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268593 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_1268593 : Nat := 118140960795 + 1268593 * 2 ^ 59
def prefixEnd_1268593 : Nat := 4983230072969 + 3 ^ 40 * 1268593 * 2
def baseEnd_1268593 : Nat := 651397963929260357753353

theorem tailTrace_1268593 : CollatzResearch.WordTrace tailWord_1268593 prefixEnd_1268593 651397963929260357753353 := by
  unfold tailWord_1268593
  simp only [CollatzResearch.WordTrace]
  refine ⟨46269387893111694280450433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30846258595407796186966955 46269387893111694280450433)
  ·
    refine ⟨34702040919833770710337825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46269387893111694280450433 34702040919833770710337825)
    ·
      refine ⟨26026530689875328032753369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34702040919833770710337825 26026530689875328032753369)
      ·
        refine ⟨19519898017406496024565027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26026530689875328032753369 19519898017406496024565027)
        ·
          refine ⟨29279847026109744036847541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19519898017406496024565027 29279847026109744036847541)
          ·
            refine ⟨2744985658697788503454457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29279847026109744036847541 2744985658697788503454457)
            ·
              refine ⟨2058739244023341377590843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2744985658697788503454457 2058739244023341377590843)
              ·
                refine ⟨3088108866035012066386265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058739244023341377590843 3088108866035012066386265)
                ·
                  refine ⟨2316081649526259049789699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3088108866035012066386265 2316081649526259049789699)
                  ·
                    refine ⟨3474122474289388574684549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2316081649526259049789699 3474122474289388574684549)
                    ·
                      refine ⟨651397963929260357753353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3474122474289388574684549 651397963929260357753353)
                      ·
                        rfl

theorem cell23_1268593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_1268593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268593 prefixEnd_1268593 := by exact prefixLift 1268593
  have htrace : WordTrace (prefixWord ++ tailWord_1268593) baseStart_1268593 baseEnd_1268593 := by
    simpa [prefixWord, tailWord_1268593, baseEnd_1268593] using wordTrace_append hprefix tailTrace_1268593
  have hstable : (prefixWord ++ tailWord_1268593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268593).length < 2 ^ (prefixWord ++ tailWord_1268593).sum := by decide
  have hdescent : baseEnd_1268593 < baseStart_1268593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268599 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 10]
def baseStart_1268599 : Nat := 118140960795 + 1268599 * 2 ^ 59
def prefixEnd_1268599 : Nat := 4983230072969 + 3 ^ 40 * 1268599 * 2
def baseEnd_1268599 : Nat := 72377893868131926030925

theorem tailTrace_1268599 : CollatzResearch.WordTrace tailWord_1268599 prefixEnd_1268599 72377893868131926030925 := by
  unfold tailWord_1268599
  simp only [CollatzResearch.WordTrace]
  refine ⟨46269606731089957305168851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30846404487393304870112567 46269606731089957305168851)
  ·
    refine ⟨69404410096634935957753277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46269606731089957305168851 69404410096634935957753277)
    ·
      refine ⟨26026653786238100984157479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69404410096634935957753277 26026653786238100984157479)
      ·
        refine ⟨39039980679357151476236219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26026653786238100984157479 39039980679357151476236219)
        ·
          refine ⟨58559971019035727214354329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39039980679357151476236219 58559971019035727214354329)
          ·
            refine ⟨43919978264276795410765747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58559971019035727214354329 43919978264276795410765747)
            ·
              refine ⟨65879967396415193116148621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43919978264276795410765747 65879967396415193116148621)
              ·
                refine ⟨24704987773655697418555733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65879967396415193116148621 24704987773655697418555733)
                ·
                  refine ⟨72377893868131926030925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24704987773655697418555733 72377893868131926030925)
                  ·
                    rfl

theorem cell23_1268599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 10].length) (baseStart_1268599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268599 prefixEnd_1268599 := by exact prefixLift 1268599
  have htrace : WordTrace (prefixWord ++ tailWord_1268599) baseStart_1268599 baseEnd_1268599 := by
    simpa [prefixWord, tailWord_1268599, baseEnd_1268599] using wordTrace_append hprefix tailTrace_1268599
  have hstable : (prefixWord ++ tailWord_1268599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268599).length < 2 ^ (prefixWord ++ tailWord_1268599).sum := by decide
  have hdescent : baseEnd_1268599 < baseStart_1268599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268613 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 3]
def baseStart_1268613 : Nat := 118140960795 + 1268613 * 2 ^ 59
def prefixEnd_1268613 : Nat := 4983230072969 + 3 ^ 40 * 1268613 * 2
def baseEnd_1268613 : Nat := 651408233542350279503261

theorem tailTrace_1268613 : CollatzResearch.WordTrace tailWord_1268613 prefixEnd_1268613 651408233542350279503261 := by
  unfold tailWord_1268613
  simp only [CollatzResearch.WordTrace]
  refine ⟨46270117353039237696178493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30846744902026158464118995 46270117353039237696178493)
  ·
    refine ⟨17351294007389714136066935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46270117353039237696178493 17351294007389714136066935)
    ·
      refine ⟨26026941011084571204100403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17351294007389714136066935 26026941011084571204100403)
      ·
        refine ⟨39040411516626856806150605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26026941011084571204100403 39040411516626856806150605)
        ·
          refine ⟨14640154318735071302306477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39040411516626856806150605 14640154318735071302306477)
          ·
            refine ⟨5490057869525651738364929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14640154318735071302306477 5490057869525651738364929)
            ·
              refine ⟨4117543402144238803773697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490057869525651738364929 4117543402144238803773697)
              ·
                refine ⟨3088157551608179102830273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4117543402144238803773697 3088157551608179102830273)
                ·
                  refine ⟨2316118163706134327122705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3088157551608179102830273 2316118163706134327122705)
                  ·
                    refine ⟨1737088622779600745342029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316118163706134327122705 1737088622779600745342029)
                    ·
                      refine ⟨651408233542350279503261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1737088622779600745342029 651408233542350279503261)
                      ·
                        rfl

theorem cell23_1268613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_1268613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268613 prefixEnd_1268613 := by exact prefixLift 1268613
  have htrace : WordTrace (prefixWord ++ tailWord_1268613) baseStart_1268613 baseEnd_1268613 := by
    simpa [prefixWord, tailWord_1268613, baseEnd_1268613] using wordTrace_append hprefix tailTrace_1268613
  have hstable : (prefixWord ++ tailWord_1268613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268613).length < 2 ^ (prefixWord ++ tailWord_1268613).sum := by decide
  have hdescent : baseEnd_1268613 < baseStart_1268613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268643 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 3]
def baseStart_1268643 : Nat := 118140960795 + 1268643 * 2 ^ 59
def prefixEnd_1268643 : Nat := 4983230072969 + 3 ^ 40 * 1268643 * 2
def baseEnd_1268643 : Nat := 651423637961985162128123

theorem tailTrace_1268643 : CollatzResearch.WordTrace tailWord_1268643 prefixEnd_1268643 651423637961985162128123 := by
  unfold tailWord_1268643
  simp only [CollatzResearch.WordTrace]
  refine ⟨46271211542930552819770583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30847474361953701879847055 46271211542930552819770583)
  ·
    refine ⟨69406817314395829229655875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46271211542930552819770583 69406817314395829229655875)
    ·
      refine ⟨104110225971593743844483813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69406817314395829229655875 104110225971593743844483813)
      ·
        refine ⟨19520667369673826970840715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104110225971593743844483813 19520667369673826970840715)
        ·
          refine ⟨29281001054510740456261073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19520667369673826970840715 29281001054510740456261073)
          ·
            refine ⟨21960750790883055342195805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29281001054510740456261073 21960750790883055342195805)
            ·
              refine ⟨8235281546581145753323427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21960750790883055342195805 8235281546581145753323427)
              ·
                refine ⟨12352922319871718629985141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235281546581145753323427 12352922319871718629985141)
                ·
                  refine ⟨1158086467487973621561107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12352922319871718629985141 1158086467487973621561107)
                  ·
                    refine ⟨1737129701231960432341661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1158086467487973621561107 1737129701231960432341661)
                    ·
                      refine ⟨651423637961985162128123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1737129701231960432341661 651423637961985162128123)
                      ·
                        rfl

theorem cell23_1268643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_1268643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268643 prefixEnd_1268643 := by exact prefixLift 1268643
  have htrace : WordTrace (prefixWord ++ tailWord_1268643) baseStart_1268643 baseEnd_1268643 := by
    simpa [prefixWord, tailWord_1268643, baseEnd_1268643] using wordTrace_append hprefix tailTrace_1268643
  have hstable : (prefixWord ++ tailWord_1268643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268643).length < 2 ^ (prefixWord ++ tailWord_1268643).sum := by decide
  have hdescent : baseEnd_1268643 < baseStart_1268643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268647 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1268647 : Nat := 118140960795 + 1268647 * 2 ^ 59
def prefixEnd_1268647 : Nat := 4983230072969 + 3 ^ 40 * 1268647 * 2
def baseEnd_1268647 : Nat := 651425691884603146478105

theorem tailTrace_1268647 : CollatzResearch.WordTrace tailWord_1268647 prefixEnd_1268647 651425691884603146478105 := by
  unfold tailWord_1268647
  simp only [CollatzResearch.WordTrace]
  refine ⟨46271357434916061502916195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30847571623277374335277463 46271357434916061502916195)
  ·
    refine ⟨69407036152374092254374293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46271357434916061502916195 69407036152374092254374293)
    ·
      refine ⟨3253454819642535574423795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69407036152374092254374293 3253454819642535574423795)
      ·
        refine ⟨4880182229463803361635693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253454819642535574423795 4880182229463803361635693)
        ·
          refine ⟨1830068336048926260613385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4880182229463803361635693 1830068336048926260613385)
          ·
            refine ⟨1372551252036694695460039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830068336048926260613385 1372551252036694695460039)
            ·
              refine ⟨2058826878055042043190059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372551252036694695460039 2058826878055042043190059)
              ·
                refine ⟨3088240317082563064785089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058826878055042043190059 3088240317082563064785089)
                ·
                  refine ⟨2316180237811922298588817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3088240317082563064785089 2316180237811922298588817)
                  ·
                    refine ⟨1737135178358941723941613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316180237811922298588817 1737135178358941723941613)
                    ·
                      refine ⟨651425691884603146478105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1737135178358941723941613 651425691884603146478105)
                      ·
                        rfl

theorem cell23_1268647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1268647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268647 prefixEnd_1268647 := by exact prefixLift 1268647
  have htrace : WordTrace (prefixWord ++ tailWord_1268647) baseStart_1268647 baseEnd_1268647 := by
    simpa [prefixWord, tailWord_1268647, baseEnd_1268647] using wordTrace_append hprefix tailTrace_1268647
  have hstable : (prefixWord ++ tailWord_1268647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268647).length < 2 ^ (prefixWord ++ tailWord_1268647).sum := by decide
  have hdescent : baseEnd_1268647 < baseStart_1268647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268670 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_1268670 : Nat := 118140960795 + 1268670 * 2 ^ 59
def prefixEnd_1268670 : Nat := 4983230072969 + 3 ^ 40 * 1268670 * 2
def baseEnd_1268670 : Nat := 651437501939656556490499

theorem tailTrace_1268670 : CollatzResearch.WordTrace tailWord_1268670 prefixEnd_1268670 651437501939656556490499 := by
  unfold tailWord_1268670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784024539229092053875433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30848130875888490954002309 5784024539229092053875433)
  ·
    refine ⟨4338018404421819040406575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5784024539229092053875433 4338018404421819040406575)
    ·
      refine ⟨6507027606632728560609863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4338018404421819040406575 6507027606632728560609863)
      ·
        refine ⟨9760541409949092840914795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6507027606632728560609863 9760541409949092840914795)
        ·
          refine ⟨14640812114923639261372193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9760541409949092840914795 14640812114923639261372193)
          ·
            refine ⟨10980609086192729446029145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14640812114923639261372193 10980609086192729446029145)
            ·
              refine ⟨8235456814644547084521859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10980609086192729446029145 8235456814644547084521859)
              ·
                refine ⟨12353185221966820626782789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235456814644547084521859 12353185221966820626782789)
                ·
                  refine ⟨2316222229118778867521773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12353185221966820626782789 2316222229118778867521773)
                  ·
                    refine ⟨868583335919542075320665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2316222229118778867521773 868583335919542075320665)
                    ·
                      refine ⟨651437501939656556490499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868583335919542075320665 651437501939656556490499)
                      ·
                        rfl

theorem cell23_1268670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_1268670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268670 prefixEnd_1268670 := by exact prefixLift 1268670
  have htrace : WordTrace (prefixWord ++ tailWord_1268670) baseStart_1268670 baseEnd_1268670 := by
    simpa [prefixWord, tailWord_1268670, baseEnd_1268670] using wordTrace_append hprefix tailTrace_1268670
  have hstable : (prefixWord ++ tailWord_1268670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268670).length < 2 ^ (prefixWord ++ tailWord_1268670).sum := by decide
  have hdescent : baseEnd_1268670 < baseStart_1268670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268790 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1268790 : Nat := 118140960795 + 1268790 * 2 ^ 59
def prefixEnd_1268790 : Nat := 4983230072969 + 3 ^ 40 * 1268790 * 2
def baseEnd_1268790 : Nat := 651499119618196086989947

theorem tailTrace_1268790 : CollatzResearch.WordTrace tailWord_1268790 prefixEnd_1268790 651499119618196086989947 := by
  unfold tailWord_1268790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2892285817087374807835739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30851048715598664616914549 2892285817087374807835739)
  ·
    refine ⟨4338428725631062211753609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2892285817087374807835739 4338428725631062211753609)
    ·
      refine ⟨3253821544223296658815207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4338428725631062211753609 3253821544223296658815207)
      ·
        refine ⟨4880732316334944988222811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253821544223296658815207 4880732316334944988222811)
        ·
          refine ⟨7321098474502417482334217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4880732316334944988222811 7321098474502417482334217)
          ·
            refine ⟨5490823855876813111750663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7321098474502417482334217 5490823855876813111750663)
            ·
              refine ⟨8236235783815219667625995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5490823855876813111750663 8236235783815219667625995)
              ·
                refine ⟨12354353675722829501438993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8236235783815219667625995 12354353675722829501438993)
                ·
                  refine ⟨9265765256792122126079245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12354353675722829501438993 9265765256792122126079245)
                  ·
                    refine ⟨3474661971297045797279717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9265765256792122126079245 3474661971297045797279717)
                    ·
                      refine ⟨651499119618196086989947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3474661971297045797279717 651499119618196086989947)
                      ·
                        rfl

theorem cell23_1268790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1268790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268790 prefixEnd_1268790 := by exact prefixLift 1268790
  have htrace : WordTrace (prefixWord ++ tailWord_1268790) baseStart_1268790 baseEnd_1268790 := by
    simpa [prefixWord, tailWord_1268790, baseEnd_1268790] using wordTrace_append hprefix tailTrace_1268790
  have hstable : (prefixWord ++ tailWord_1268790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268790).length < 2 ^ (prefixWord ++ tailWord_1268790).sum := by decide
  have hdescent : baseEnd_1268790 < baseStart_1268790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268803 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4]
def baseStart_1268803 : Nat := 118140960795 + 1268803 * 2 ^ 59
def prefixEnd_1268803 : Nat := 4983230072969 + 3 ^ 40 * 1268803 * 2
def baseEnd_1268803 : Nat := 651505794866704536127387

theorem tailTrace_1268803 : CollatzResearch.WordTrace tailWord_1268803 prefixEnd_1268803 651505794866704536127387 := by
  unfold tailWord_1268803
  simp only [CollatzResearch.WordTrace]
  refine ⟨46277047222350900145595063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30851364814900600097063375 46277047222350900145595063)
  ·
    refine ⟨69415570833526350218392595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46277047222350900145595063 69415570833526350218392595)
    ·
      refine ⟨104123356250289525327588893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69415570833526350218392595 104123356250289525327588893)
      ·
        refine ⟨39046258593858571997845835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104123356250289525327588893 39046258593858571997845835)
        ·
          refine ⟨58569387890787857996768753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39046258593858571997845835 58569387890787857996768753)
          ·
            refine ⟨43927040918090893497576565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58569387890787857996768753 43927040918090893497576565)
            ·
              refine ⟨4118160086071021265397803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43927040918090893497576565 4118160086071021265397803)
              ·
                refine ⟨6177240129106531898096705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118160086071021265397803 6177240129106531898096705)
                ·
                  refine ⟨4632930096829898923572529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177240129106531898096705 4632930096829898923572529)
                  ·
                    refine ⟨3474697572622424192679397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4632930096829898923572529 3474697572622424192679397)
                    ·
                      refine ⟨651505794866704536127387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3474697572622424192679397 651505794866704536127387)
                      ·
                        rfl

theorem cell23_1268803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_1268803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268803 prefixEnd_1268803 := by exact prefixLift 1268803
  have htrace : WordTrace (prefixWord ++ tailWord_1268803) baseStart_1268803 baseEnd_1268803 := by
    simpa [prefixWord, tailWord_1268803, baseEnd_1268803] using wordTrace_append hprefix tailTrace_1268803
  have hstable : (prefixWord ++ tailWord_1268803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268803).length < 2 ^ (prefixWord ++ tailWord_1268803).sum := by decide
  have hdescent : baseEnd_1268803 < baseStart_1268803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268807 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 1, 4, 2]
def baseStart_1268807 : Nat := 118140960795 + 1268807 * 2 ^ 59
def prefixEnd_1268807 : Nat := 4983230072969 + 3 ^ 40 * 1268807 * 2
def baseEnd_1268807 : Nat := 651507848789322520477369

theorem tailTrace_1268807 : CollatzResearch.WordTrace tailWord_1268807 prefixEnd_1268807 651507848789322520477369 := by
  unfold tailWord_1268807
  simp only [CollatzResearch.WordTrace]
  refine ⟨46277193114336408828740675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30851462076224272552493783 46277193114336408828740675)
  ·
    refine ⟨69415789671504613243111013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46277193114336408828740675 69415789671504613243111013)
    ·
      refine ⟨13015460563407114983083315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69415789671504613243111013 13015460563407114983083315)
      ·
        refine ⟨19523190845110672474624973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13015460563407114983083315 19523190845110672474624973)
        ·
          refine ⟨7321196566916502177984365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19523190845110672474624973 7321196566916502177984365)
          ·
            refine ⟨2745448712593688316744137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7321196566916502177984365 2745448712593688316744137)
            ·
              refine ⟨2059086534445266237558103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745448712593688316744137 2059086534445266237558103)
              ·
                refine ⟨3088629801667899356337155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059086534445266237558103 3088629801667899356337155)
                ·
                  refine ⟨4632944702501849034505733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088629801667899356337155 4632944702501849034505733)
                  ·
                    refine ⟨868677131719096693969825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4632944702501849034505733 868677131719096693969825)
                    ·
                      refine ⟨651507848789322520477369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868677131719096693969825 651507848789322520477369)
                      ·
                        rfl

theorem cell23_1268807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_1268807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268807 prefixEnd_1268807 := by exact prefixLift 1268807
  have htrace : WordTrace (prefixWord ++ tailWord_1268807) baseStart_1268807 baseEnd_1268807 := by
    simpa [prefixWord, tailWord_1268807, baseEnd_1268807] using wordTrace_append hprefix tailTrace_1268807
  have hstable : (prefixWord ++ tailWord_1268807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268807).length < 2 ^ (prefixWord ++ tailWord_1268807).sum := by decide
  have hdescent : baseEnd_1268807 < baseStart_1268807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268823 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 3]
def baseStart_1268823 : Nat := 118140960795 + 1268823 * 2 ^ 59
def prefixEnd_1268823 : Nat := 4983230072969 + 3 ^ 40 * 1268823 * 2
def baseEnd_1268823 : Nat := 651516064479794457877295

theorem tailTrace_1268823 : CollatzResearch.WordTrace tailWord_1268823 prefixEnd_1268823 651516064479794457877295 := by
  unfold tailWord_1268823
  simp only [CollatzResearch.WordTrace]
  refine ⟨46277776682278443561323123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30851851121518962374215415 46277776682278443561323123)
  ·
    refine ⟨69416665023417665341984685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46277776682278443561323123 69416665023417665341984685)
    ·
      refine ⟨26031249383781624503244257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69416665023417665341984685 26031249383781624503244257)
      ·
        refine ⟨19523437037836218377433193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26031249383781624503244257 19523437037836218377433193)
        ·
          refine ⟨14642577778377163783074895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19523437037836218377433193 14642577778377163783074895)
          ·
            refine ⟨21963866667565745674612343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14642577778377163783074895 21963866667565745674612343)
            ·
              refine ⟨32945800001348618511918515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21963866667565745674612343 32945800001348618511918515)
              ·
                refine ⟨49418700002022927767877773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32945800001348618511918515 49418700002022927767877773)
                ·
                  refine ⟨18532012500758597912954165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49418700002022927767877773 18532012500758597912954165)
                  ·
                    refine ⟨1737376171946118554339453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18532012500758597912954165 1737376171946118554339453)
                    ·
                      refine ⟨651516064479794457877295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1737376171946118554339453 651516064479794457877295)
                      ·
                        rfl

theorem cell23_1268823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_1268823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268823 prefixEnd_1268823 := by exact prefixLift 1268823
  have htrace : WordTrace (prefixWord ++ tailWord_1268823) baseStart_1268823 baseEnd_1268823 := by
    simpa [prefixWord, tailWord_1268823, baseEnd_1268823] using wordTrace_append hprefix tailTrace_1268823
  have hstable : (prefixWord ++ tailWord_1268823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268823).length < 2 ^ (prefixWord ++ tailWord_1268823).sum := by decide
  have hdescent : baseEnd_1268823 < baseStart_1268823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268880 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 4, 4, 2]
def baseStart_1268880 : Nat := 118140960795 + 1268880 * 2 ^ 59
def prefixEnd_1268880 : Nat := 4983230072969 + 3 ^ 40 * 1268880 * 2
def baseEnd_1268880 : Nat := 651545332877100734864533

theorem tailTrace_1268880 : CollatzResearch.WordTrace tailWord_1268880 prefixEnd_1268880 651545332877100734864533 := by
  unfold tailWord_1268880
  simp only [CollatzResearch.WordTrace]
  refine ⟨23139927821535971148074047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30853237095381294864098729 23139927821535971148074047)
  ·
    refine ⟨34709891732303956722111071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23139927821535971148074047 34709891732303956722111071)
    ·
      refine ⟨52064837598455935083166607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34709891732303956722111071 52064837598455935083166607)
      ·
        refine ⟨78097256397683902624749911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52064837598455935083166607 78097256397683902624749911)
        ·
          refine ⟨117145884596525853937124867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78097256397683902624749911 117145884596525853937124867)
          ·
            refine ⟨175718826894788780905687301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117145884596525853937124867 175718826894788780905687301)
            ·
              refine ⟨32947280042772896419816369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175718826894788780905687301 32947280042772896419816369)
              ·
                refine ⟨24710460032079672314862277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32947280042772896419816369 24710460032079672314862277)
                ·
                  refine ⟨4633211256014938559036677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24710460032079672314862277 4633211256014938559036677)
                  ·
                    refine ⟨868727110502800979819377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4633211256014938559036677 868727110502800979819377)
                    ·
                      refine ⟨651545332877100734864533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868727110502800979819377 651545332877100734864533)
                      ·
                        rfl

theorem cell23_1268880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 4, 2].length) (baseStart_1268880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268880 prefixEnd_1268880 := by exact prefixLift 1268880
  have htrace : WordTrace (prefixWord ++ tailWord_1268880) baseStart_1268880 baseEnd_1268880 := by
    simpa [prefixWord, tailWord_1268880, baseEnd_1268880] using wordTrace_append hprefix tailTrace_1268880
  have hstable : (prefixWord ++ tailWord_1268880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268880).length < 2 ^ (prefixWord ++ tailWord_1268880).sum := by decide
  have hdescent : baseEnd_1268880 < baseStart_1268880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1268943 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_1268943 : Nat := 118140960795 + 1268943 * 2 ^ 59
def prefixEnd_1268943 : Nat := 4983230072969 + 3 ^ 40 * 1268943 * 2
def baseEnd_1268943 : Nat := 651577682158333988376743

theorem tailTrace_1268943 : CollatzResearch.WordTrace tailWord_1268943 prefixEnd_1268943 651577682158333988376743 := by
  unfold tailWord_1268943
  simp only [CollatzResearch.WordTrace]
  refine ⟨46282153441843704055691483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30854768961229136037127655 46282153441843704055691483)
  ·
    refine ⟨69423230162765556083537225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46282153441843704055691483 69423230162765556083537225)
    ·
      refine ⟨52067422622074167062652919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69423230162765556083537225 52067422622074167062652919)
      ·
        refine ⟨78101133933111250593979379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52067422622074167062652919 78101133933111250593979379)
        ·
          refine ⟨117151700899666875890969069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78101133933111250593979379 117151700899666875890969069)
          ·
            refine ⟨43931887837375078459113401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117151700899666875890969069 43931887837375078459113401)
            ·
              refine ⟨32948915878031308844335051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43931887837375078459113401 32948915878031308844335051)
              ·
                refine ⟨49423373817046963266502577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32948915878031308844335051 49423373817046963266502577)
                ·
                  refine ⟨37067530362785222449876933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49423373817046963266502577 37067530362785222449876933)
                  ·
                    refine ⟨6950161943022229209351925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37067530362785222449876933 6950161943022229209351925)
                    ·
                      refine ⟨651577682158333988376743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6950161943022229209351925 651577682158333988376743)
                      ·
                        rfl

theorem cell23_1268943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_1268943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1268943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1268943 prefixEnd_1268943 := by exact prefixLift 1268943
  have htrace : WordTrace (prefixWord ++ tailWord_1268943) baseStart_1268943 baseEnd_1268943 := by
    simpa [prefixWord, tailWord_1268943, baseEnd_1268943] using wordTrace_append hprefix tailTrace_1268943
  have hstable : (prefixWord ++ tailWord_1268943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1268943).length < 2 ^ (prefixWord ++ tailWord_1268943).sum := by decide
  have hdescent : baseEnd_1268943 < baseStart_1268943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1268943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269004 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 1, 1, 4]
def baseStart_1269004 : Nat := 118140960795 + 1269004 * 2 ^ 59
def prefixEnd_1269004 : Nat := 4983230072969 + 3 ^ 40 * 1269004 * 2
def baseEnd_1269004 : Nat := 651609004478258249713963

theorem tailTrace_1269004 : CollatzResearch.WordTrace tailWord_1269004 prefixEnd_1269004 651609004478258249713963 := by
  unfold tailWord_1269004
  simp only [CollatzResearch.WordTrace]
  refine ⟨23142189147311355736831033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30856252196415140982441377 23142189147311355736831033)
  ·
    refine ⟨17356641860483516802623275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23142189147311355736831033 17356641860483516802623275)
    ·
      refine ⟨26034962790725275203934913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17356641860483516802623275 26034962790725275203934913)
      ·
        refine ⟨19526222093043956402951185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26034962790725275203934913 19526222093043956402951185)
        ·
          refine ⟨14644666569782967302213389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19526222093043956402951185 14644666569782967302213389)
          ·
            refine ⟨5491749963668612738330021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14644666569782967302213389 5491749963668612738330021)
            ·
              refine ⟨1029703118187864888436879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5491749963668612738330021 1029703118187864888436879)
              ·
                refine ⟨1544554677281797332655319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029703118187864888436879 1544554677281797332655319)
                ·
                  refine ⟨2316832015922695998982979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544554677281797332655319 2316832015922695998982979)
                  ·
                    refine ⟨3475248023884043998474469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2316832015922695998982979 3475248023884043998474469)
                    ·
                      refine ⟨651609004478258249713963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3475248023884043998474469 651609004478258249713963)
                      ·
                        rfl

theorem cell23_1269004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_1269004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269004 prefixEnd_1269004 := by exact prefixLift 1269004
  have htrace : WordTrace (prefixWord ++ tailWord_1269004) baseStart_1269004 baseEnd_1269004 := by
    simpa [prefixWord, tailWord_1269004, baseEnd_1269004] using wordTrace_append hprefix tailTrace_1269004
  have hstable : (prefixWord ++ tailWord_1269004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269004).length < 2 ^ (prefixWord ++ tailWord_1269004).sum := by decide
  have hdescent : baseEnd_1269004 < baseStart_1269004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269021 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1269021 : Nat := 118140960795 + 1269021 * 2 ^ 59
def prefixEnd_1269021 : Nat := 4983230072969 + 3 ^ 40 * 1269021 * 2
def baseEnd_1269021 : Nat := 651617733649384683201385

theorem tailTrace_1269021 : CollatzResearch.WordTrace tailWord_1269021 prefixEnd_1269021 651617733649384683201385 := by
  unfold tailWord_1269021
  simp only [CollatzResearch.WordTrace]
  refine ⟨46284998335561123377030917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30856665557040748918020611 46284998335561123377030917)
  ·
    refine ⟨8678437187917710633193297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46284998335561123377030917 8678437187917710633193297)
    ·
      refine ⟨6508827890938282974894973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8678437187917710633193297 6508827890938282974894973)
      ·
        refine ⟨2440810459101856115585615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6508827890938282974894973 2440810459101856115585615)
        ·
          refine ⟨3661215688652784173378423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440810459101856115585615 3661215688652784173378423)
          ·
            refine ⟨5491823532979176260067635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3661215688652784173378423 5491823532979176260067635)
            ·
              refine ⟨8237735299468764390101453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5491823532979176260067635 8237735299468764390101453)
              ·
                refine ⟨3089150737300786646288045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8237735299468764390101453 3089150737300786646288045)
                ·
                  refine ⟨1158431526487794992358017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3089150737300786646288045 1158431526487794992358017)
                  ·
                    refine ⟨868823644865846244268513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1158431526487794992358017 868823644865846244268513)
                    ·
                      refine ⟨651617733649384683201385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868823644865846244268513 651617733649384683201385)
                      ·
                        rfl

theorem cell23_1269021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1269021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269021 prefixEnd_1269021 := by exact prefixLift 1269021
  have htrace : WordTrace (prefixWord ++ tailWord_1269021) baseStart_1269021 baseEnd_1269021 := by
    simpa [prefixWord, tailWord_1269021, baseEnd_1269021] using wordTrace_append hprefix tailTrace_1269021
  have hstable : (prefixWord ++ tailWord_1269021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269021).length < 2 ^ (prefixWord ++ tailWord_1269021).sum := by decide
  have hdescent : baseEnd_1269021 < baseStart_1269021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269034 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1269034 : Nat := 118140960795 + 1269034 * 2 ^ 59
def prefixEnd_1269034 : Nat := 4983230072969 + 3 ^ 40 * 1269034 * 2
def baseEnd_1269034 : Nat := 651624408897893132338825

theorem tailTrace_1269034 : CollatzResearch.WordTrace tailWord_1269034 prefixEnd_1269034 651624408897893132338825 := by
  unfold tailWord_1269034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11571368121128506649313539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30856981656342684398169437 11571368121128506649313539)
  ·
    refine ⟨17357052181692759973970309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11571368121128506649313539 17357052181692759973970309)
    ·
      refine ⟨3254447284067392495119433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17357052181692759973970309 3254447284067392495119433)
      ·
        refine ⟨2440835463050544371339575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3254447284067392495119433 2440835463050544371339575)
        ·
          refine ⟨3661253194575816557009363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440835463050544371339575 3661253194575816557009363)
          ·
            refine ⟨5491879791863724835514045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3661253194575816557009363 5491879791863724835514045)
            ·
              refine ⟨2059454921948896813317767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5491879791863724835514045 2059454921948896813317767)
              ·
                refine ⟨3089182382923345219976651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059454921948896813317767 3089182382923345219976651)
                ·
                  refine ⟨4633773574385017829964977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089182382923345219976651 4633773574385017829964977)
                  ·
                    refine ⟨3475330180788763372473733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633773574385017829964977 3475330180788763372473733)
                    ·
                      refine ⟨651624408897893132338825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3475330180788763372473733 651624408897893132338825)
                      ·
                        rfl

theorem cell23_1269034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1269034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269034 prefixEnd_1269034 := by exact prefixLift 1269034
  have htrace : WordTrace (prefixWord ++ tailWord_1269034) baseStart_1269034 baseEnd_1269034 := by
    simpa [prefixWord, tailWord_1269034, baseEnd_1269034] using wordTrace_append hprefix tailTrace_1269034
  have hstable : (prefixWord ++ tailWord_1269034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269034).length < 2 ^ (prefixWord ++ tailWord_1269034).sum := by decide
  have hdescent : baseEnd_1269034 < baseStart_1269034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269050 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1269050 : Nat := 118140960795 + 1269050 * 2 ^ 59
def prefixEnd_1269050 : Nat := 4983230072969 + 3 ^ 40 * 1269050 * 2
def baseEnd_1269050 : Nat := 651632624588365069738751

theorem tailTrace_1269050 : CollatzResearch.WordTrace tailWord_1269050 prefixEnd_1269050 651632624588365069738751 := by
  unfold tailWord_1269050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11571514013114015332459151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30857370701637374219891069 11571514013114015332459151)
  ·
    refine ⟨17357271019671022998688727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11571514013114015332459151 17357271019671022998688727)
    ·
      refine ⟨26035906529506534498033091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17357271019671022998688727 26035906529506534498033091)
      ·
        refine ⟨39053859794259801747049637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26035906529506534498033091 39053859794259801747049637)
        ·
          refine ⟨7322598711423712827571807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39053859794259801747049637 7322598711423712827571807)
          ·
            refine ⟨10983898067135569241357711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322598711423712827571807 10983898067135569241357711)
            ·
              refine ⟨16475847100703353862036567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10983898067135569241357711 16475847100703353862036567)
              ·
                refine ⟨24713770651055030793054851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16475847100703353862036567 24713770651055030793054851)
                ·
                  refine ⟨37070655976582546189582277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24713770651055030793054851 37070655976582546189582277)
                  ·
                    refine ⟨6950747995609227410546677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37070655976582546189582277 6950747995609227410546677)
                    ·
                      refine ⟨651632624588365069738751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6950747995609227410546677 651632624588365069738751)
                      ·
                        rfl

theorem cell23_1269050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1269050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269050 prefixEnd_1269050 := by exact prefixLift 1269050
  have htrace : WordTrace (prefixWord ++ tailWord_1269050) baseStart_1269050 baseEnd_1269050 := by
    simpa [prefixWord, tailWord_1269050, baseEnd_1269050] using wordTrace_append hprefix tailTrace_1269050
  have hstable : (prefixWord ++ tailWord_1269050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269050).length < 2 ^ (prefixWord ++ tailWord_1269050).sum := by decide
  have hdescent : baseEnd_1269050 < baseStart_1269050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269054 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1269054 : Nat := 118140960795 + 1269054 * 2 ^ 59
def prefixEnd_1269054 : Nat := 4983230072969 + 3 ^ 40 * 1269054 * 2
def baseEnd_1269054 : Nat := 651634678510983054088733

theorem tailTrace_1269054 : CollatzResearch.WordTrace tailWord_1269054 prefixEnd_1269054 651634678510983054088733 := by
  unfold tailWord_1269054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5785775243055196251622777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30857467962961046675321477 5785775243055196251622777)
  ·
    refine ⟨4339331432291397188717083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5785775243055196251622777 4339331432291397188717083)
    ·
      refine ⟨6508997148437095783075625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339331432291397188717083 6508997148437095783075625)
      ·
        refine ⟨4881747861327821837306719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6508997148437095783075625 4881747861327821837306719)
        ·
          refine ⟨7322621791991732755960079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881747861327821837306719 7322621791991732755960079)
          ·
            refine ⟨10983932687987599133940119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322621791991732755960079 10983932687987599133940119)
            ·
              refine ⟨16475899031981398700910179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10983932687987599133940119 16475899031981398700910179)
              ·
                refine ⟨24713848547972098051365269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16475899031981398700910179 24713848547972098051365269)
                ·
                  refine ⟨1158461650686192096157747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24713848547972098051365269 1158461650686192096157747)
                  ·
                    refine ⟨1737692476029288144236621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1158461650686192096157747 1737692476029288144236621)
                    ·
                      refine ⟨651634678510983054088733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1737692476029288144236621 651634678510983054088733)
                      ·
                        rfl

theorem cell23_1269054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1269054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269054 prefixEnd_1269054 := by exact prefixLift 1269054
  have htrace : WordTrace (prefixWord ++ tailWord_1269054) baseStart_1269054 baseEnd_1269054 := by
    simpa [prefixWord, tailWord_1269054, baseEnd_1269054] using wordTrace_append hprefix tailTrace_1269054
  have hstable : (prefixWord ++ tailWord_1269054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269054).length < 2 ^ (prefixWord ++ tailWord_1269054).sum := by decide
  have hdescent : baseEnd_1269054 < baseStart_1269054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269078 : List Nat := [5, 2, 3, 1, 1, 1, 2, 8]
def baseStart_1269078 : Nat := 118140960795 + 1269078 * 2 ^ 59
def prefixEnd_1269078 : Nat := 4983230072969 + 3 ^ 40 * 1269078 * 2
def baseEnd_1269078 : Nat := 24135074149877442969949

theorem tailTrace_1269078 : CollatzResearch.WordTrace tailWord_1269078 prefixEnd_1269078 24135074149877442969949 := by
  unfold tailWord_1269078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2892942331022163881990993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30858051530903081407903925 2892942331022163881990993)
  ·
    refine ⟨2169706748266622911493245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2892942331022163881990993 2169706748266622911493245)
    ·
      refine ⟨813640030599983591809967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2169706748266622911493245 813640030599983591809967)
      ·
        refine ⟨1220460045899975387714951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813640030599983591809967 1220460045899975387714951)
        ·
          refine ⟨1830690068849963081572427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220460045899975387714951 1830690068849963081572427)
          ·
            refine ⟨2746035103274944622358641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830690068849963081572427 2746035103274944622358641)
            ·
              refine ⟨2059526327456208466768981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746035103274944622358641 2059526327456208466768981)
              ·
                refine ⟨24135074149877442969949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2059526327456208466768981 24135074149877442969949)
                ·
                  rfl

theorem cell23_1269078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_1269078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269078 prefixEnd_1269078 := by exact prefixLift 1269078
  have htrace : WordTrace (prefixWord ++ tailWord_1269078) baseStart_1269078 baseEnd_1269078 := by
    simpa [prefixWord, tailWord_1269078, baseEnd_1269078] using wordTrace_append hprefix tailTrace_1269078
  have hstable : (prefixWord ++ tailWord_1269078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269078).length < 2 ^ (prefixWord ++ tailWord_1269078).sum := by decide
  have hdescent : baseEnd_1269078 < baseStart_1269078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269080 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1269080 : Nat := 118140960795 + 1269080 * 2 ^ 59
def prefixEnd_1269080 : Nat := 4983230072969 + 3 ^ 40 * 1269080 * 2
def baseEnd_1269080 : Nat := 651648029007999952363613

theorem tailTrace_1269080 : CollatzResearch.WordTrace tailWord_1269080 prefixEnd_1269080 651648029007999952363613 := by
  unfold tailWord_1269080
  simp only [CollatzResearch.WordTrace]
  refine ⟨23143575121173688226714347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30858100161564917635619129 23143575121173688226714347)
  ·
    refine ⟨34715362681760532340071521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23143575121173688226714347 34715362681760532340071521)
    ·
      refine ⟨26036522011320399255053641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34715362681760532340071521 26036522011320399255053641)
      ·
        refine ⟨19527391508490299441290231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26036522011320399255053641 19527391508490299441290231)
        ·
          refine ⟨29291087262735449161935347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19527391508490299441290231 29291087262735449161935347)
          ·
            refine ⟨43936630894103173742903021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29291087262735449161935347 43936630894103173742903021)
            ·
              refine ⟨16476236585288690153588633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43936630894103173742903021 16476236585288690153588633)
              ·
                refine ⟨12357177438966517615191475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16476236585288690153588633 12357177438966517615191475)
                ·
                  refine ⟨18535766158449776422787213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12357177438966517615191475 18535766158449776422787213)
                  ·
                    refine ⟨6950912309418666158545205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18535766158449776422787213 6950912309418666158545205)
                    ·
                      refine ⟨651648029007999952363613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6950912309418666158545205 651648029007999952363613)
                      ·
                        rfl

theorem cell23_1269080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1269080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269080 prefixEnd_1269080 := by exact prefixLift 1269080
  have htrace : WordTrace (prefixWord ++ tailWord_1269080) baseStart_1269080 baseEnd_1269080 := by
    simpa [prefixWord, tailWord_1269080, baseEnd_1269080] using wordTrace_append hprefix tailTrace_1269080
  have hstable : (prefixWord ++ tailWord_1269080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269080).length < 2 ^ (prefixWord ++ tailWord_1269080).sum := by decide
  have hdescent : baseEnd_1269080 < baseStart_1269080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269088 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 2, 1, 3]
def baseStart_1269088 : Nat := 118140960795 + 1269088 * 2 ^ 59
def prefixEnd_1269088 : Nat := 4983230072969 + 3 ^ 40 * 1269088 * 2
def baseEnd_1269088 : Nat := 651652136853235921063577

theorem tailTrace_1269088 : CollatzResearch.WordTrace tailWord_1269088 prefixEnd_1269088 651652136853235921063577 := by
  unfold tailWord_1269088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23143721013159196909859959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30858294684212262546479945 23143721013159196909859959)
  ·
    refine ⟨34715581519738795364789939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23143721013159196909859959 34715581519738795364789939)
    ·
      refine ⟨52073372279608193047184909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34715581519738795364789939 52073372279608193047184909)
      ·
        refine ⟨19527514604853072392694341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52073372279608193047184909 19527514604853072392694341)
        ·
          refine ⟨3661408988409951073630189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19527514604853072392694341 3661408988409951073630189)
          ·
            refine ⟨1373028370653731652611321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3661408988409951073630189 1373028370653731652611321)
            ·
              refine ⟨1029771277990298739458491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373028370653731652611321 1029771277990298739458491)
              ·
                refine ⟨1544656916985448109187737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029771277990298739458491 1544656916985448109187737)
                ·
                  refine ⟨1158492687739086081890803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544656916985448109187737 1158492687739086081890803)
                  ·
                    refine ⟨1737739031608629122836205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1158492687739086081890803 1737739031608629122836205)
                    ·
                      refine ⟨651652136853235921063577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1737739031608629122836205 651652136853235921063577)
                      ·
                        rfl

theorem cell23_1269088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_1269088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269088 prefixEnd_1269088 := by exact prefixLift 1269088
  have htrace : WordTrace (prefixWord ++ tailWord_1269088) baseStart_1269088 baseEnd_1269088 := by
    simpa [prefixWord, tailWord_1269088, baseEnd_1269088] using wordTrace_append hprefix tailTrace_1269088
  have hstable : (prefixWord ++ tailWord_1269088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269088).length < 2 ^ (prefixWord ++ tailWord_1269088).sum := by decide
  have hdescent : baseEnd_1269088 < baseStart_1269088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269128 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_1269128 : Nat := 118140960795 + 1269128 * 2 ^ 59
def prefixEnd_1269128 : Nat := 4983230072969 + 3 ^ 40 * 1269128 * 2
def baseEnd_1269128 : Nat := 651672676079415764563393

theorem tailTrace_1269128 : CollatzResearch.WordTrace tailWord_1269128 prefixEnd_1269128 651672676079415764563393 := by
  unfold tailWord_1269128
  simp only [CollatzResearch.WordTrace]
  refine ⟨23144450473086740325588019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30859267297448987100784025 23144450473086740325588019)
  ·
    refine ⟨34716675709630110488382029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23144450473086740325588019 34716675709630110488382029)
    ·
      refine ⟨13018753391111291433143261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34716675709630110488382029 13018753391111291433143261)
      ·
        refine ⟨4882032521666734287428723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13018753391111291433143261 4882032521666734287428723)
        ·
          refine ⟨7323048782500101431143085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882032521666734287428723 7323048782500101431143085)
          ·
            refine ⟨2746143293437538036678657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7323048782500101431143085 2746143293437538036678657)
            ·
              refine ⟨2059607470078153527508993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746143293437538036678657 2059607470078153527508993)
              ·
                refine ⟨1544705602558615145631745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059607470078153527508993 1544705602558615145631745)
                ·
                  refine ⟨1158529201918961359223809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544705602558615145631745 1158529201918961359223809)
                  ·
                    refine ⟨868896901439221019417857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1158529201918961359223809 868896901439221019417857)
                    ·
                      refine ⟨651672676079415764563393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868896901439221019417857 651672676079415764563393)
                      ·
                        rfl

theorem cell23_1269128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_1269128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269128 prefixEnd_1269128 := by exact prefixLift 1269128
  have htrace : WordTrace (prefixWord ++ tailWord_1269128) baseStart_1269128 baseEnd_1269128 := by
    simpa [prefixWord, tailWord_1269128, baseEnd_1269128] using wordTrace_append hprefix tailTrace_1269128
  have hstable : (prefixWord ++ tailWord_1269128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269128).length < 2 ^ (prefixWord ++ tailWord_1269128).sum := by decide
  have hdescent : baseEnd_1269128 < baseStart_1269128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269184 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 2, 4, 2]
def baseStart_1269184 : Nat := 118140960795 + 1269184 * 2 ^ 59
def prefixEnd_1269184 : Nat := 4983230072969 + 3 ^ 40 * 1269184 * 2
def baseEnd_1269184 : Nat := 651701430996067545463135

theorem tailTrace_1269184 : CollatzResearch.WordTrace tailWord_1269184 prefixEnd_1269184 651701430996067545463135 := by
  unfold tailWord_1269184
  simp only [CollatzResearch.WordTrace]
  refine ⟨23145471716985301107607303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30860628955980401476809737 23145471716985301107607303)
  ·
    refine ⟨34718207575477951661410955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23145471716985301107607303 34718207575477951661410955)
    ·
      refine ⟨52077311363216927492116433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34718207575477951661410955 52077311363216927492116433)
      ·
        refine ⟨39057983522412695619087325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52077311363216927492116433 39057983522412695619087325)
        ·
          refine ⟨14646743820904760857157747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39057983522412695619087325 14646743820904760857157747)
          ·
            refine ⟨21970115731357141285736621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14646743820904760857157747 21970115731357141285736621)
            ·
              refine ⟨8238793399258927982151233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21970115731357141285736621 8238793399258927982151233)
              ·
                refine ⟨6179095049444195986613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8238793399258927982151233 6179095049444195986613425)
                ·
                  refine ⟨4634321287083146989960069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6179095049444195986613425 4634321287083146989960069)
                  ·
                    refine ⟨868935241328090060617513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4634321287083146989960069 868935241328090060617513)
                    ·
                      refine ⟨651701430996067545463135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 868935241328090060617513 651701430996067545463135)
                      ·
                        rfl

theorem cell23_1269184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_1269184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269184 prefixEnd_1269184 := by exact prefixLift 1269184
  have htrace : WordTrace (prefixWord ++ tailWord_1269184) baseStart_1269184 baseEnd_1269184 := by
    simpa [prefixWord, tailWord_1269184, baseEnd_1269184] using wordTrace_append hprefix tailTrace_1269184
  have hstable : (prefixWord ++ tailWord_1269184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269184).length < 2 ^ (prefixWord ++ tailWord_1269184).sum := by decide
  have hdescent : baseEnd_1269184 < baseStart_1269184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269194 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_1269194 : Nat := 118140960795 + 1269194 * 2 ^ 59
def prefixEnd_1269194 : Nat := 4983230072969 + 3 ^ 40 * 1269194 * 2
def baseEnd_1269194 : Nat := 217235521934204168779363

theorem tailTrace_1269194 : CollatzResearch.WordTrace tailWord_1269194 prefixEnd_1269194 217235521934204168779363 := by
  unfold tailWord_1269194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11572827040983593480769659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30860872109289582615385757 11572827040983593480769659)
  ·
    refine ⟨17359240561475390221154489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11572827040983593480769659 17359240561475390221154489)
    ·
      refine ⟨13019430421106542665865867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17359240561475390221154489 13019430421106542665865867)
      ·
        refine ⟨19529145631659813998798801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13019430421106542665865867 19529145631659813998798801)
        ·
          refine ⟨14646859223744860499099101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19529145631659813998798801 14646859223744860499099101)
          ·
            refine ⟨5492572208904322687162163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14646859223744860499099101 5492572208904322687162163)
            ·
              refine ⟨8238858313356484030743245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492572208904322687162163 8238858313356484030743245)
              ·
                refine ⟨3089571867508681511528717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8238858313356484030743245 3089571867508681511528717)
                ·
                  refine ⟨1158589450315755566823269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3089571867508681511528717 1158589450315755566823269)
                  ·
                    refine ⟨217235521934204168779363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1158589450315755566823269 217235521934204168779363)
                    ·
                      rfl

theorem cell23_1269194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_1269194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269194 prefixEnd_1269194 := by exact prefixLift 1269194
  have htrace : WordTrace (prefixWord ++ tailWord_1269194) baseStart_1269194 baseEnd_1269194 := by
    simpa [prefixWord, tailWord_1269194, baseEnd_1269194] using wordTrace_append hprefix tailTrace_1269194
  have hstable : (prefixWord ++ tailWord_1269194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269194).length < 2 ^ (prefixWord ++ tailWord_1269194).sum := by decide
  have hdescent : baseEnd_1269194 < baseStart_1269194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269207 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 6]
def baseStart_1269207 : Nat := 118140960795 + 1269207 * 2 ^ 59
def prefixEnd_1269207 : Nat := 4983230072969 + 3 ^ 40 * 1269207 * 2
def baseEnd_1269207 : Nat := 72412582339013439497281

theorem tailTrace_1269207 : CollatzResearch.WordTrace tailWord_1269207 prefixEnd_1269207 72412582339013439497281 := by
  unfold tailWord_1269207
  simp only [CollatzResearch.WordTrace]
  refine ⟨46291782312887277143301875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30861188208591518095534583 46291782312887277143301875)
  ·
    refine ⟨69437673469330915714952813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46291782312887277143301875 69437673469330915714952813)
    ·
      refine ⟨26039127550999093393107305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69437673469330915714952813 26039127550999093393107305)
      ·
        refine ⟨19529345663249320044830479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26039127550999093393107305 19529345663249320044830479)
        ·
          refine ⟨29294018494873980067245719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19529345663249320044830479 29294018494873980067245719)
          ·
            refine ⟨43941027742310970100868579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29294018494873980067245719 43941027742310970100868579)
            ·
              refine ⟨65911541613466455151302869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43941027742310970100868579 65911541613466455151302869)
              ·
                refine ⟨1544801756565620042608661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65911541613466455151302869 1544801756565620042608661)
                ·
                  refine ⟨72412582339013439497281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1544801756565620042608661 72412582339013439497281)
                  ·
                    rfl

theorem cell23_1269207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 6].length) (baseStart_1269207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269207 prefixEnd_1269207 := by exact prefixLift 1269207
  have htrace : WordTrace (prefixWord ++ tailWord_1269207) baseStart_1269207 baseEnd_1269207 := by
    simpa [prefixWord, tailWord_1269207, baseEnd_1269207] using wordTrace_append hprefix tailTrace_1269207
  have hstable : (prefixWord ++ tailWord_1269207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269207).length < 2 ^ (prefixWord ++ tailWord_1269207).sum := by decide
  have hdescent : baseEnd_1269207 < baseStart_1269207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269301 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1269301 : Nat := 118140960795 + 1269301 * 2 ^ 59
def prefixEnd_1269301 : Nat := 4983230072969 + 3 ^ 40 * 1269301 * 2
def baseEnd_1269301 : Nat := 217253836077547862566699

theorem tailTrace_1269301 : CollatzResearch.WordTrace tailWord_1269301 prefixEnd_1269301 217253836077547862566699 := by
  unfold tailWord_1269301
  simp only [CollatzResearch.WordTrace]
  refine ⟨46295210774546731197223757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30863473849697820798149171 46295210774546731197223757)
  ·
    refine ⟨17360704040455024198958909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46295210774546731197223757 17360704040455024198958909)
    ·
      refine ⟨6510264015170634074609591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17360704040455024198958909 6510264015170634074609591)
      ·
        refine ⟨9765396022755951111914387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510264015170634074609591 9765396022755951111914387)
        ·
          refine ⟨14648094034133926667871581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9765396022755951111914387 14648094034133926667871581)
          ·
            refine ⟨5493035262800222500451843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14648094034133926667871581 5493035262800222500451843)
            ·
              refine ⟨8239552894200333750677765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5493035262800222500451843 8239552894200333750677765)
              ·
                refine ⟨1544916167662562578252081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8239552894200333750677765 1544916167662562578252081)
                ·
                  refine ⟨1158687125746921933689061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544916167662562578252081 1158687125746921933689061)
                  ·
                    refine ⟨217253836077547862566699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1158687125746921933689061 217253836077547862566699)
                    ·
                      rfl

theorem cell23_1269301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1269301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269301 prefixEnd_1269301 := by exact prefixLift 1269301
  have htrace : WordTrace (prefixWord ++ tailWord_1269301) baseStart_1269301 baseEnd_1269301 := by
    simpa [prefixWord, tailWord_1269301, baseEnd_1269301] using wordTrace_append hprefix tailTrace_1269301
  have hstable : (prefixWord ++ tailWord_1269301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269301).length < 2 ^ (prefixWord ++ tailWord_1269301).sum := by decide
  have hdescent : baseEnd_1269301 < baseStart_1269301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269302 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1269302 : Nat := 118140960795 + 1269302 * 2 ^ 59
def prefixEnd_1269302 : Nat := 4983230072969 + 3 ^ 40 * 1269302 * 2
def baseEnd_1269302 : Nat := 651762021713298083787593

theorem tailTrace_1269302 : CollatzResearch.WordTrace tailWord_1269302 prefixEnd_1269302 651762021713298083787593 := by
  unfold tailWord_1269302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893452952971444273000635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30863498165028738912006773 2893452952971444273000635)
  ·
    refine ⟨4340179429457166409500953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2893452952971444273000635 4340179429457166409500953)
    ·
      refine ⟨3255134572092874807125715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4340179429457166409500953 3255134572092874807125715)
      ·
        refine ⟨4882701858139312210688573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255134572092874807125715 4882701858139312210688573)
        ·
          refine ⟨1831013196802242079008215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4882701858139312210688573 1831013196802242079008215)
          ·
            refine ⟨2746519795203363118512323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831013196802242079008215 2746519795203363118512323)
            ·
              refine ⟨4119779692805044677768485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746519795203363118512323 4119779692805044677768485)
              ·
                refine ⟨772458692400945877081591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4119779692805044677768485 772458692400945877081591)
                ·
                  refine ⟨1158688038601418815622387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772458692400945877081591 1158688038601418815622387)
                  ·
                    refine ⟨1738032057902128223433581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1158688038601418815622387 1738032057902128223433581)
                    ·
                      refine ⟨651762021713298083787593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738032057902128223433581 651762021713298083787593)
                      ·
                        rfl

theorem cell23_1269302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1269302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269302 prefixEnd_1269302 := by exact prefixLift 1269302
  have htrace : WordTrace (prefixWord ++ tailWord_1269302) baseStart_1269302 baseEnd_1269302 := by
    simpa [prefixWord, tailWord_1269302, baseEnd_1269302] using wordTrace_append hprefix tailTrace_1269302
  have hstable : (prefixWord ++ tailWord_1269302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269302).length < 2 ^ (prefixWord ++ tailWord_1269302).sum := by decide
  have hdescent : baseEnd_1269302 < baseStart_1269302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269327 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 4, 7]
def baseStart_1269327 : Nat := 118140960795 + 1269327 * 2 ^ 59
def prefixEnd_1269327 : Nat := 4983230072969 + 3 ^ 40 * 1269327 * 2
def baseEnd_1269327 : Nat := 217258286243220161991659

theorem tailTrace_1269327 : CollatzResearch.WordTrace tailWord_1269327 prefixEnd_1269327 217258286243220161991659 := by
  unfold tailWord_1269327
  simp only [CollatzResearch.WordTrace]
  refine ⟨46296159072452537637670235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30864106048301691758446823 46296159072452537637670235)
  ·
    refine ⟨69444238608678806456505353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46296159072452537637670235 69444238608678806456505353)
    ·
      refine ⟨52083178956509104842379015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69444238608678806456505353 52083178956509104842379015)
      ·
        refine ⟨78124768434763657263568523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52083178956509104842379015 78124768434763657263568523)
        ·
          refine ⟨117187152652145485895352785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78124768434763657263568523 117187152652145485895352785)
          ·
            refine ⟨87890364489109114421514589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117187152652145485895352785 87890364489109114421514589)
            ·
              refine ⟨32958886683415917908067971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87890364489109114421514589 32958886683415917908067971)
              ·
                refine ⟨49438330025123876862101957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32958886683415917908067971 49438330025123876862101957)
                ·
                  refine ⟨9269686879710726911644117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49438330025123876862101957 9269686879710726911644117)
                  ·
                    refine ⟨217258286243220161991659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9269686879710726911644117 217258286243220161991659)
                    ·
                      rfl

theorem cell23_1269327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_1269327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269327 prefixEnd_1269327 := by exact prefixLift 1269327
  have htrace : WordTrace (prefixWord ++ tailWord_1269327) baseStart_1269327 baseEnd_1269327 := by
    simpa [prefixWord, tailWord_1269327, baseEnd_1269327] using wordTrace_append hprefix tailTrace_1269327
  have hstable : (prefixWord ++ tailWord_1269327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269327).length < 2 ^ (prefixWord ++ tailWord_1269327).sum := by decide
  have hdescent : baseEnd_1269327 < baseStart_1269327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269471 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1269471 : Nat := 118140960795 + 1269471 * 2 ^ 59
def prefixEnd_1269471 : Nat := 4983230072969 + 3 ^ 40 * 1269471 * 2
def baseEnd_1269471 : Nat := 651848799943907922574315

theorem tailTrace_1269471 : CollatzResearch.WordTrace tailWord_1269471 prefixEnd_1269471 651848799943907922574315 := by
  unfold tailWord_1269471
  simp only [CollatzResearch.WordTrace]
  refine ⟨46301411183930850230912267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30867607455953900153941511 46301411183930850230912267)
  ·
    refine ⟨69452116775896275346368401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46301411183930850230912267 69452116775896275346368401)
    ·
      refine ⟨52089087581922206509776301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69452116775896275346368401 52089087581922206509776301)
      ·
        refine ⟨19533407843220827441166113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52089087581922206509776301 19533407843220827441166113)
        ·
          refine ⟨14650055882415620580874585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19533407843220827441166113 14650055882415620580874585)
          ·
            refine ⟨10987541911811715435655939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14650055882415620580874585 10987541911811715435655939)
            ·
              refine ⟨16481312867717573153483909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10987541911811715435655939 16481312867717573153483909)
              ·
                refine ⟨3090246162697044966278233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16481312867717573153483909 3090246162697044966278233)
                ·
                  refine ⟨2317684622022783724708675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090246162697044966278233 2317684622022783724708675)
                  ·
                    refine ⟨3476526933034175587063013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2317684622022783724708675 3476526933034175587063013)
                    ·
                      refine ⟨651848799943907922574315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3476526933034175587063013 651848799943907922574315)
                      ·
                        rfl

theorem cell23_1269471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1269471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269471 prefixEnd_1269471 := by exact prefixLift 1269471
  have htrace : WordTrace (prefixWord ++ tailWord_1269471) baseStart_1269471 baseEnd_1269471 := by
    simpa [prefixWord, tailWord_1269471, baseEnd_1269471] using wordTrace_append hprefix tailTrace_1269471
  have hstable : (prefixWord ++ tailWord_1269471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269471).length < 2 ^ (prefixWord ++ tailWord_1269471).sum := by decide
  have hdescent : baseEnd_1269471 < baseStart_1269471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269481 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 3, 4]
def baseStart_1269481 : Nat := 118140960795 + 1269481 * 2 ^ 59
def prefixEnd_1269481 : Nat := 4983230072969 + 3 ^ 40 * 1269481 * 2
def baseEnd_1269481 : Nat := 217284644916817627816423

theorem tailTrace_1269481 : CollatzResearch.WordTrace tailWord_1269481 prefixEnd_1269481 217284644916817627816423 := by
  unfold tailWord_1269481
  simp only [CollatzResearch.WordTrace]
  refine ⟨46301775913894621938776297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30867850609263081292517531 46301775913894621938776297)
  ·
    refine ⟨34726331935420966454082223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46301775913894621938776297 34726331935420966454082223)
    ·
      refine ⟨52089497903131449681123335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34726331935420966454082223 52089497903131449681123335)
      ·
        refine ⟨78134246854697174521685003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52089497903131449681123335 78134246854697174521685003)
        ·
          refine ⟨117201370282045761782527505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78134246854697174521685003 117201370282045761782527505)
          ·
            refine ⟨87901027711534321336895629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117201370282045761782527505 87901027711534321336895629)
            ·
              refine ⟨32962885391825370501335861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87901027711534321336895629 32962885391825370501335861)
              ·
                refine ⟨3090270505483628484500237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32962885391825370501335861 3090270505483628484500237)
                ·
                  refine ⟨1158851439556360681687589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3090270505483628484500237 1158851439556360681687589)
                  ·
                    refine ⟨217284644916817627816423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1158851439556360681687589 217284644916817627816423)
                    ·
                      rfl

theorem cell23_1269481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_1269481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269481 prefixEnd_1269481 := by exact prefixLift 1269481
  have htrace : WordTrace (prefixWord ++ tailWord_1269481) baseStart_1269481 baseEnd_1269481 := by
    simpa [prefixWord, tailWord_1269481, baseEnd_1269481] using wordTrace_append hprefix tailTrace_1269481
  have hstable : (prefixWord ++ tailWord_1269481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269481).length < 2 ^ (prefixWord ++ tailWord_1269481).sum := by decide
  have hdescent : baseEnd_1269481 < baseStart_1269481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269491 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 3]
def baseStart_1269491 : Nat := 118140960795 + 1269491 * 2 ^ 59
def prefixEnd_1269491 : Nat := 4983230072969 + 3 ^ 40 * 1269491 * 2
def baseEnd_1269491 : Nat := 651859069556997844324223

theorem tailTrace_1269491 : CollatzResearch.WordTrace tailWord_1269491 prefixEnd_1269491 651859069556997844324223 := by
  unfold tailWord_1269491
  simp only [CollatzResearch.WordTrace]
  refine ⟨46302140643858393646640327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30868093762572262431093551 46302140643858393646640327)
  ·
    refine ⟨69453210965787590469960491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46302140643858393646640327 69453210965787590469960491)
    ·
      refine ⟨104179816448681385704940737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69453210965787590469960491 104179816448681385704940737)
      ·
        refine ⟨78134862336511039278705553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104179816448681385704940737 78134862336511039278705553)
        ·
          refine ⟨58601146752383279459029165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78134862336511039278705553 58601146752383279459029165)
          ·
            refine ⟨21975430032143729797135937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58601146752383279459029165 21975430032143729797135937)
            ·
              refine ⟨16481572524107797347851953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21975430032143729797135937 16481572524107797347851953)
              ·
                refine ⟨12361179393080848010888965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16481572524107797347851953 12361179393080848010888965)
                ·
                  refine ⟨2317721136202659002041681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12361179393080848010888965 2317721136202659002041681)
                  ·
                    refine ⟨1738290852151994251531261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2317721136202659002041681 1738290852151994251531261)
                    ·
                      refine ⟨651859069556997844324223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738290852151994251531261 651859069556997844324223)
                      ·
                        rfl

theorem cell23_1269491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 3].length) (baseStart_1269491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269491 prefixEnd_1269491 := by exact prefixLift 1269491
  have htrace : WordTrace (prefixWord ++ tailWord_1269491) baseStart_1269491 baseEnd_1269491 := by
    simpa [prefixWord, tailWord_1269491, baseEnd_1269491] using wordTrace_append hprefix tailTrace_1269491
  have hstable : (prefixWord ++ tailWord_1269491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269491).length < 2 ^ (prefixWord ++ tailWord_1269491).sum := by decide
  have hdescent : baseEnd_1269491 < baseStart_1269491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269502 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1269502 : Nat := 118140960795 + 1269502 * 2 ^ 59
def prefixEnd_1269502 : Nat := 4983230072969 + 3 ^ 40 * 1269502 * 2
def baseEnd_1269502 : Nat := 217288239281399100428891

theorem tailTrace_1269502 : CollatzResearch.WordTrace tailWord_1269502 prefixEnd_1269502 217288239281399100428891 := by
  unfold tailWord_1269502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787817730852317815661345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30868361231212361683527173 5787817730852317815661345)
  ·
    refine ⟨4340863298139238361746009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5787817730852317815661345 4340863298139238361746009)
    ·
      refine ⟨3255647473604428771309507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4340863298139238361746009 3255647473604428771309507)
      ·
        refine ⟨4883471210406643156964261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255647473604428771309507 4883471210406643156964261)
        ·
          refine ⟨915650851951245591930799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4883471210406643156964261 915650851951245591930799)
          ·
            refine ⟨1373476277926868387896199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915650851951245591930799 1373476277926868387896199)
            ·
              refine ⟨2060214416890302581844299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373476277926868387896199 2060214416890302581844299)
              ·
                refine ⟨3090321625335453872766449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060214416890302581844299 3090321625335453872766449)
                ·
                  refine ⟨2317741219001590404574837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090321625335453872766449 2317741219001590404574837)
                  ·
                    refine ⟨217288239281399100428891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2317741219001590404574837 217288239281399100428891)
                    ·
                      rfl

theorem cell23_1269502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1269502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269502 prefixEnd_1269502 := by exact prefixLift 1269502
  have htrace : WordTrace (prefixWord ++ tailWord_1269502) baseStart_1269502 baseEnd_1269502 := by
    simpa [prefixWord, tailWord_1269502, baseEnd_1269502] using wordTrace_append hprefix tailTrace_1269502
  have hstable : (prefixWord ++ tailWord_1269502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269502).length < 2 ^ (prefixWord ++ tailWord_1269502).sum := by decide
  have hdescent : baseEnd_1269502 < baseStart_1269502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269508 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1269508 : Nat := 118140960795 + 1269508 * 2 ^ 59
def prefixEnd_1269508 : Nat := 4983230072969 + 3 ^ 40 * 1269508 * 2
def baseEnd_1269508 : Nat := 651867798728124277811645

theorem tailTrace_1269508 : CollatzResearch.WordTrace tailWord_1269508 prefixEnd_1269508 651867798728124277811645 := by
  unfold tailWord_1269508
  simp only [CollatzResearch.WordTrace]
  refine ⟨23151380342398402775004589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30868507123197870366672785 23151380342398402775004589)
  ·
    refine ⟨8681767628399401040626721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23151380342398402775004589 8681767628399401040626721)
    ·
      refine ⟨6511325721299550780470041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8681767628399401040626721 6511325721299550780470041)
      ·
        refine ⟨4883494290974663085352531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511325721299550780470041 4883494290974663085352531)
        ·
          refine ⟨7325241436461994628028797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883494290974663085352531 7325241436461994628028797)
          ·
            refine ⟨2746965538673247985510799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7325241436461994628028797 2746965538673247985510799)
            ·
              refine ⟨4120448308009871978266199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746965538673247985510799 4120448308009871978266199)
              ·
                refine ⟨6180672462014807967399299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120448308009871978266199 6180672462014807967399299)
                ·
                  refine ⟨9271008693022211951098949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180672462014807967399299 9271008693022211951098949)
                  ·
                    refine ⟨1738314129941664740831053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9271008693022211951098949 1738314129941664740831053)
                    ·
                      refine ⟨651867798728124277811645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738314129941664740831053 651867798728124277811645)
                      ·
                        rfl

theorem cell23_1269508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1269508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269508 prefixEnd_1269508 := by exact prefixLift 1269508
  have htrace : WordTrace (prefixWord ++ tailWord_1269508) baseStart_1269508 baseEnd_1269508 := by
    simpa [prefixWord, tailWord_1269508, baseEnd_1269508] using wordTrace_append hprefix tailTrace_1269508
  have hstable : (prefixWord ++ tailWord_1269508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269508).length < 2 ^ (prefixWord ++ tailWord_1269508).sum := by decide
  have hdescent : baseEnd_1269508 < baseStart_1269508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269548 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 1, 5, 2]
def baseStart_1269548 : Nat := 118140960795 + 1269548 * 2 ^ 59
def prefixEnd_1269548 : Nat := 4983230072969 + 3 ^ 40 * 1269548 * 2
def baseEnd_1269548 : Nat := 651888337954304121311461

theorem tailTrace_1269548 : CollatzResearch.WordTrace tailWord_1269548 prefixEnd_1269548 651888337954304121311461 := by
  unfold tailWord_1269548
  simp only [CollatzResearch.WordTrace]
  refine ⟨23152109802325946190732649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30869479736434594920976865 23152109802325946190732649)
  ·
    refine ⟨17364082351744459643049487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23152109802325946190732649 17364082351744459643049487)
    ·
      refine ⟨26046123527616689464574231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17364082351744459643049487 26046123527616689464574231)
      ·
        refine ⟨39069185291425034196861347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26046123527616689464574231 39069185291425034196861347)
        ·
          refine ⟨58603777937137551295292021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39069185291425034196861347 58603777937137551295292021)
          ·
            refine ⟨5494104181606645433933627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58603777937137551295292021 5494104181606645433933627)
            ·
              refine ⟨8241156272409968150900441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494104181606645433933627 8241156272409968150900441)
              ·
                refine ⟨6180867204307476113175331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8241156272409968150900441 6180867204307476113175331)
                ·
                  refine ⟨9271300806461214169762997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180867204307476113175331 9271300806461214169762997)
                  ·
                    refine ⟨869184450605738828415281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9271300806461214169762997 869184450605738828415281)
                    ·
                      refine ⟨651888337954304121311461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869184450605738828415281 651888337954304121311461)
                      ·
                        rfl

theorem cell23_1269548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_1269548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269548 prefixEnd_1269548 := by exact prefixLift 1269548
  have htrace : WordTrace (prefixWord ++ tailWord_1269548) baseStart_1269548 baseEnd_1269548 := by
    simpa [prefixWord, tailWord_1269548, baseEnd_1269548] using wordTrace_append hprefix tailTrace_1269548
  have hstable : (prefixWord ++ tailWord_1269548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269548).length < 2 ^ (prefixWord ++ tailWord_1269548).sum := by decide
  have hdescent : baseEnd_1269548 < baseStart_1269548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269565 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1269565 : Nat := 118140960795 + 1269565 * 2 ^ 59
def prefixEnd_1269565 : Nat := 4983230072969 + 3 ^ 40 * 1269565 * 2
def baseEnd_1269565 : Nat := 651897067125430554798883

theorem tailTrace_1269565 : CollatzResearch.WordTrace tailWord_1269565 prefixEnd_1269565 651897067125430554798883 := by
  unfold tailWord_1269565
  simp only [CollatzResearch.WordTrace]
  refine ⟨46304839645590304284834149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30869893097060202856556099 46304839645590304284834149)
  ·
    refine ⟨8682157433548182053406403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46304839645590304284834149 8682157433548182053406403)
    ·
      refine ⟨13023236150322273080109605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8682157433548182053406403 13023236150322273080109605)
      ·
        refine ⟨2441856778185426202520551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13023236150322273080109605 2441856778185426202520551)
        ·
          refine ⟨3662785167278139303780827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441856778185426202520551 3662785167278139303780827)
          ·
            refine ⟨5494177750917208955671241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662785167278139303780827 5494177750917208955671241)
            ·
              refine ⟨4120633313187906716753431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5494177750917208955671241 4120633313187906716753431)
              ·
                refine ⟨6180949969781860075130147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120633313187906716753431 6180949969781860075130147)
                ·
                  refine ⟨9271424954672790112695221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180949969781860075130147 9271424954672790112695221)
                  ·
                    refine ⟨869196089500574073065177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9271424954672790112695221 869196089500574073065177)
                    ·
                      refine ⟨651897067125430554798883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869196089500574073065177 651897067125430554798883)
                      ·
                        rfl

theorem cell23_1269565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1269565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269565 prefixEnd_1269565 := by exact prefixLift 1269565
  have htrace : WordTrace (prefixWord ++ tailWord_1269565) baseStart_1269565 baseEnd_1269565 := by
    simpa [prefixWord, tailWord_1269565, baseEnd_1269565] using wordTrace_append hprefix tailTrace_1269565
  have hstable : (prefixWord ++ tailWord_1269565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269565).length < 2 ^ (prefixWord ++ tailWord_1269565).sum := by decide
  have hdescent : baseEnd_1269565 < baseStart_1269565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269578 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_1269578 : Nat := 118140960795 + 1269578 * 2 ^ 59
def prefixEnd_1269578 : Nat := 4983230072969 + 3 ^ 40 * 1269578 * 2
def baseEnd_1269578 : Nat := 651903742373939003936323

theorem tailTrace_1269578 : CollatzResearch.WordTrace tailWord_1269578 prefixEnd_1269578 651903742373939003936323 := by
  unfold tailWord_1269578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576328448635801876264347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30870209196362138336704925 11576328448635801876264347)
  ·
    refine ⟨17364492672953702814396521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11576328448635801876264347 17364492672953702814396521)
    ·
      refine ⟨13023369504715277110797391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17364492672953702814396521 13023369504715277110797391)
      ·
        refine ⟨19535054257072915666196087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13023369504715277110797391 19535054257072915666196087)
        ·
          refine ⟨29302581385609373499294131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19535054257072915666196087 29302581385609373499294131)
          ·
            refine ⟨43953872078414060248941197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29302581385609373499294131 43953872078414060248941197)
            ·
              refine ⟨16482702029405272593352949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43953872078414060248941197 16482702029405272593352949)
              ·
                refine ⟨1545253315256744305626839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16482702029405272593352949 1545253315256744305626839)
                ·
                  refine ⟨2317879972885116458440259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545253315256744305626839 2317879972885116458440259)
                  ·
                    refine ⟨3476819959327674687660389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2317879972885116458440259 3476819959327674687660389)
                    ·
                      refine ⟨651903742373939003936323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3476819959327674687660389 651903742373939003936323)
                      ·
                        rfl

theorem cell23_1269578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_1269578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269578 prefixEnd_1269578 := by exact prefixLift 1269578
  have htrace : WordTrace (prefixWord ++ tailWord_1269578) baseStart_1269578 baseEnd_1269578 := by
    simpa [prefixWord, tailWord_1269578, baseEnd_1269578] using wordTrace_append hprefix tailTrace_1269578
  have hstable : (prefixWord ++ tailWord_1269578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269578).length < 2 ^ (prefixWord ++ tailWord_1269578).sum := by decide
  have hdescent : baseEnd_1269578 < baseStart_1269578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269589 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_1269589 : Nat := 118140960795 + 1269589 * 2 ^ 59
def prefixEnd_1269589 : Nat := 4983230072969 + 3 ^ 40 * 1269589 * 2
def baseEnd_1269589 : Nat := 651909390661138460898773

theorem tailTrace_1269589 : CollatzResearch.WordTrace tailWord_1269589 prefixEnd_1269589 651909390661138460898773 := by
  unfold tailWord_1269589
  simp only [CollatzResearch.WordTrace]
  refine ⟨46305714997503356383707821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30870476665002237589138547 46305714997503356383707821)
  ·
    refine ⟨17364643124063758643890433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46305714997503356383707821 17364643124063758643890433)
    ·
      refine ⟨13023482343047818982917825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17364643124063758643890433 13023482343047818982917825)
      ·
        refine ⟨9767611757285864237188369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13023482343047818982917825 9767611757285864237188369)
        ·
          refine ⟨7325708817964398177891277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9767611757285864237188369 7325708817964398177891277)
          ·
            refine ⟨2747140806736649316709229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7325708817964398177891277 2747140806736649316709229)
            ·
              refine ⟨1030177802526243493765961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2747140806736649316709229 1030177802526243493765961)
              ·
                refine ⟨772633351894682620324471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030177802526243493765961 772633351894682620324471)
                ·
                  refine ⟨1158950027842023930486707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772633351894682620324471 1158950027842023930486707)
                  ·
                    refine ⟨1738425041763035895730061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1158950027842023930486707 1738425041763035895730061)
                    ·
                      refine ⟨651909390661138460898773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738425041763035895730061 651909390661138460898773)
                      ·
                        rfl

theorem cell23_1269589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_1269589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269589 prefixEnd_1269589 := by exact prefixLift 1269589
  have htrace : WordTrace (prefixWord ++ tailWord_1269589) baseStart_1269589 baseEnd_1269589 := by
    simpa [prefixWord, tailWord_1269589, baseEnd_1269589] using wordTrace_append hprefix tailTrace_1269589
  have hstable : (prefixWord ++ tailWord_1269589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269589).length < 2 ^ (prefixWord ++ tailWord_1269589).sum := by decide
  have hdescent : baseEnd_1269589 < baseStart_1269589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269601 : List Nat := [1, 2, 3, 1, 1, 1, 6, 8]
def baseStart_1269601 : Nat := 118140960795 + 1269601 * 2 ^ 59
def prefixEnd_1269601 : Nat := 4983230072969 + 3 ^ 40 * 1269601 * 2
def baseEnd_1269601 : Nat := 24145020460333052368471

theorem tailTrace_1269601 : CollatzResearch.WordTrace tailWord_1269601 prefixEnd_1269601 24145020460333052368471 := by
  unfold tailWord_1269601
  simp only [CollatzResearch.WordTrace]
  refine ⟨46306152673459882433144657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30870768448973254955429771 46306152673459882433144657)
  ·
    refine ⟨34729614505094911824858493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46306152673459882433144657 34729614505094911824858493)
    ·
      refine ⟨13023605439410591934321935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34729614505094911824858493 13023605439410591934321935)
      ·
        refine ⟨19535408159115887901482903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13023605439410591934321935 19535408159115887901482903)
        ·
          refine ⟨29303112238673831852224355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19535408159115887901482903 29303112238673831852224355)
          ·
            refine ⟨43954668358010747778336533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29303112238673831852224355 43954668358010747778336533)
            ·
              refine ⟨2060375079281753802109525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43954668358010747778336533 2060375079281753802109525)
              ·
                refine ⟨24145020460333052368471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2060375079281753802109525 24145020460333052368471)
                ·
                  rfl

theorem cell23_1269601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 8].length) (baseStart_1269601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269601 prefixEnd_1269601 := by exact prefixLift 1269601
  have htrace : WordTrace (prefixWord ++ tailWord_1269601) baseStart_1269601 baseEnd_1269601 := by
    simpa [prefixWord, tailWord_1269601, baseEnd_1269601] using wordTrace_append hprefix tailTrace_1269601
  have hstable : (prefixWord ++ tailWord_1269601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269601).length < 2 ^ (prefixWord ++ tailWord_1269601).sum := by decide
  have hdescent : baseEnd_1269601 < baseStart_1269601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269608 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1269608 : Nat := 118140960795 + 1269608 * 2 ^ 59
def prefixEnd_1269608 : Nat := 4983230072969 + 3 ^ 40 * 1269608 * 2
def baseEnd_1269608 : Nat := 651919146793573886561185

theorem tailTrace_1269608 : CollatzResearch.WordTrace tailWord_1269608 prefixEnd_1269608 651919146793573886561185 := by
  unfold tailWord_1269608
  simp only [CollatzResearch.WordTrace]
  refine ⟨23153203992217261314324739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30870938656289681752432985 23153203992217261314324739)
  ·
    refine ⟨34729805988325891971487109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23153203992217261314324739 34729805988325891971487109)
    ·
      refine ⟨6511838622811104744653833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34729805988325891971487109 6511838622811104744653833)
      ·
        refine ⟨4883878967108328558490375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511838622811104744653833 4883878967108328558490375)
        ·
          refine ⟨7325818450662492837735563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883878967108328558490375 7325818450662492837735563)
          ·
            refine ⟨10988727675993739256603345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325818450662492837735563 10988727675993739256603345)
            ·
              refine ⟨8241545756995304442452509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10988727675993739256603345 8241545756995304442452509)
              ·
                refine ⟨3090579658873239165919691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8241545756995304442452509 3090579658873239165919691)
                ·
                  refine ⟨4635869488309858748879537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090579658873239165919691 4635869488309858748879537)
                  ·
                    refine ⟨3476902116232394061659653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4635869488309858748879537 3476902116232394061659653)
                    ·
                      refine ⟨651919146793573886561185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3476902116232394061659653 651919146793573886561185)
                      ·
                        rfl

theorem cell23_1269608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1269608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269608 prefixEnd_1269608 := by exact prefixLift 1269608
  have htrace : WordTrace (prefixWord ++ tailWord_1269608) baseStart_1269608 baseEnd_1269608 := by
    simpa [prefixWord, tailWord_1269608, baseEnd_1269608] using wordTrace_append hprefix tailTrace_1269608
  have hstable : (prefixWord ++ tailWord_1269608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269608).length < 2 ^ (prefixWord ++ tailWord_1269608).sum := by decide
  have hdescent : baseEnd_1269608 < baseStart_1269608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269655 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 3, 3, 2]
def baseStart_1269655 : Nat := 118140960795 + 1269655 * 2 ^ 59
def prefixEnd_1269655 : Nat := 4983230072969 + 3 ^ 40 * 1269655 * 2
def baseEnd_1269655 : Nat := 651943280384335202673469

theorem tailTrace_1269655 : CollatzResearch.WordTrace tailWord_1269655 prefixEnd_1269655 651943280384335202673469 := by
  unfold tailWord_1269655
  simp only [CollatzResearch.WordTrace]
  refine ⟨46308122215264249655610419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30872081476842833103740279 46308122215264249655610419)
  ·
    refine ⟨69462183322896374483415629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46308122215264249655610419 69462183322896374483415629)
    ·
      refine ⟨26048318746086140431280861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69462183322896374483415629 26048318746086140431280861)
      ·
        refine ⟨9768119529782302661730323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26048318746086140431280861 9768119529782302661730323)
        ·
          refine ⟨14652179294673453992595485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9768119529782302661730323 14652179294673453992595485)
          ·
            refine ⟨5494567235502545247223307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14652179294673453992595485 5494567235502545247223307)
            ·
              refine ⟨8241850853253817870834961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494567235502545247223307 8241850853253817870834961)
              ·
                refine ⟨6181388139940363403126221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8241850853253817870834961 6181388139940363403126221)
                ·
                  refine ⟨2318020552477636276172333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6181388139940363403126221 2318020552477636276172333)
                  ·
                    refine ⟨869257707179113603564625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318020552477636276172333 869257707179113603564625)
                    ·
                      refine ⟨651943280384335202673469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869257707179113603564625 651943280384335202673469)
                      ·
                        rfl

theorem cell23_1269655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_1269655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269655 prefixEnd_1269655 := by exact prefixLift 1269655
  have htrace : WordTrace (prefixWord ++ tailWord_1269655) baseStart_1269655 baseEnd_1269655 := by
    simpa [prefixWord, tailWord_1269655, baseEnd_1269655] using wordTrace_append hprefix tailTrace_1269655
  have hstable : (prefixWord ++ tailWord_1269655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269655).length < 2 ^ (prefixWord ++ tailWord_1269655).sum := by decide
  have hdescent : baseEnd_1269655 < baseStart_1269655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269701 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_1269701 : Nat := 118140960795 + 1269701 * 2 ^ 59
def prefixEnd_1269701 : Nat := 4983230072969 + 3 ^ 40 * 1269701 * 2
def baseEnd_1269701 : Nat := 651966900494442022698257

theorem tailTrace_1269701 : CollatzResearch.WordTrace tailWord_1269701 prefixEnd_1269701 651966900494442022698257 := by
  unfold tailWord_1269701
  simp only [CollatzResearch.WordTrace]
  refine ⟨46309799973097599511784957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30873199982065066341189971 46309799973097599511784957)
  ·
    refine ⟨17366174989911599816919359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46309799973097599511784957 17366174989911599816919359)
    ·
      refine ⟨26049262484867399725379039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17366174989911599816919359 26049262484867399725379039)
      ·
        refine ⟨39073893727301099588068559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26049262484867399725379039 39073893727301099588068559)
        ·
          refine ⟨58610840590951649382102839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39073893727301099588068559 58610840590951649382102839)
          ·
            refine ⟨87916260886427474073154259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58610840590951649382102839 87916260886427474073154259)
            ·
              refine ⟨131874391329641211109731389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87916260886427474073154259 131874391329641211109731389)
              ·
                refine ⟨49452896748615454166149271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131874391329641211109731389 49452896748615454166149271)
                ·
                  refine ⟨74179345122923181249223907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49452896748615454166149271 74179345122923181249223907)
                  ·
                    refine ⟨111269017684384771873835861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74179345122923181249223907 111269017684384771873835861)
                    ·
                      refine ⟨651966900494442022698257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 111269017684384771873835861 651966900494442022698257)
                      ·
                        rfl

theorem cell23_1269701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_1269701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269701 prefixEnd_1269701 := by exact prefixLift 1269701
  have htrace : WordTrace (prefixWord ++ tailWord_1269701) baseStart_1269701 baseEnd_1269701 := by
    simpa [prefixWord, tailWord_1269701, baseEnd_1269701] using wordTrace_append hprefix tailTrace_1269701
  have hstable : (prefixWord ++ tailWord_1269701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269701).length < 2 ^ (prefixWord ++ tailWord_1269701).sum := by decide
  have hdescent : baseEnd_1269701 < baseStart_1269701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269708 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 7]
def baseStart_1269708 : Nat := 118140960795 + 1269708 * 2 ^ 59
def prefixEnd_1269708 : Nat := 4983230072969 + 3 ^ 40 * 1269708 * 2
def baseEnd_1269708 : Nat := 72441166095447055034525

theorem tailTrace_1269708 : CollatzResearch.WordTrace tailWord_1269708 prefixEnd_1269708 72441166095447055034525 := by
  unfold tailWord_1269708
  simp only [CollatzResearch.WordTrace]
  refine ⟨23155027642036119853644889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30873370189381493138193185 23155027642036119853644889)
  ·
    refine ⟨17366270731527089890233667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23155027642036119853644889 17366270731527089890233667)
    ·
      refine ⟨26049406097290634835350501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17366270731527089890233667 26049406097290634835350501)
      ·
        refine ⟨4884263643241994031628219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26049406097290634835350501 4884263643241994031628219)
        ·
          refine ⟨7326395464862991047442329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4884263643241994031628219 7326395464862991047442329)
          ·
            refine ⟨5494796598647243285581747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7326395464862991047442329 5494796598647243285581747)
            ·
              refine ⟨8242194897970864928372621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494796598647243285581747 8242194897970864928372621)
              ·
                refine ⟨3090823086739074348139733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8242194897970864928372621 3090823086739074348139733)
                ·
                  refine ⟨72441166095447055034525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3090823086739074348139733 72441166095447055034525)
                  ·
                    rfl

theorem cell23_1269708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_1269708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269708 prefixEnd_1269708 := by exact prefixLift 1269708
  have htrace : WordTrace (prefixWord ++ tailWord_1269708) baseStart_1269708 baseEnd_1269708 := by
    simpa [prefixWord, tailWord_1269708, baseEnd_1269708] using wordTrace_append hprefix tailTrace_1269708
  have hstable : (prefixWord ++ tailWord_1269708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269708).length < 2 ^ (prefixWord ++ tailWord_1269708).sum := by decide
  have hdescent : baseEnd_1269708 < baseStart_1269708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269719 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 2, 2, 2]
def baseStart_1269719 : Nat := 118140960795 + 1269719 * 2 ^ 59
def prefixEnd_1269719 : Nat := 4983230072969 + 3 ^ 40 * 1269719 * 2
def baseEnd_1269719 : Nat := 651976143146222952273175

theorem tailTrace_1269719 : CollatzResearch.WordTrace tailWord_1269719 prefixEnd_1269719 651976143146222952273175 := by
  unfold tailWord_1269719
  simp only [CollatzResearch.WordTrace]
  refine ⟨46310456487032388585940211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30873637658021592390626807 46310456487032388585940211)
  ·
    refine ⟨69465684730548582878910317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46310456487032388585940211 69465684730548582878910317)
    ·
      refine ⟨26049631773955718579591369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69465684730548582878910317 26049631773955718579591369)
      ·
        refine ⟨19537223830466788934693527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26049631773955718579591369 19537223830466788934693527)
        ·
          refine ⟨29305835745700183402040291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19537223830466788934693527 29305835745700183402040291)
          ·
            refine ⟨43958753618550275103060437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29305835745700183402040291 43958753618550275103060437)
            ·
              refine ⟨1030283287934772072727979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43958753618550275103060437 1030283287934772072727979)
              ·
                refine ⟨1545424931902158109091969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030283287934772072727979 1545424931902158109091969)
                ·
                  refine ⟨1159068698926618581818977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1545424931902158109091969 1159068698926618581818977)
                  ·
                    refine ⟨869301524194963936364233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1159068698926618581818977 869301524194963936364233)
                    ·
                      refine ⟨651976143146222952273175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869301524194963936364233 651976143146222952273175)
                      ·
                        rfl

theorem cell23_1269719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_1269719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269719 prefixEnd_1269719 := by exact prefixLift 1269719
  have htrace : WordTrace (prefixWord ++ tailWord_1269719) baseStart_1269719 baseEnd_1269719 := by
    simpa [prefixWord, tailWord_1269719, baseEnd_1269719] using wordTrace_append hprefix tailTrace_1269719
  have hstable : (prefixWord ++ tailWord_1269719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269719).length < 2 ^ (prefixWord ++ tailWord_1269719).sum := by decide
  have hdescent : baseEnd_1269719 < baseStart_1269719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269738 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1269738 : Nat := 118140960795 + 1269738 * 2 ^ 59
def prefixEnd_1269738 : Nat := 4983230072969 + 3 ^ 40 * 1269738 * 2
def baseEnd_1269738 : Nat := 217328633092886125978529

theorem tailTrace_1269738 : CollatzResearch.WordTrace tailWord_1269738 prefixEnd_1269738 217328633092886125978529 := by
  unfold tailWord_1269738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11577787368490888707720467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30874099649309036553921245 11577787368490888707720467)
  ·
    refine ⟨17366681052736333061580701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11577787368490888707720467 17366681052736333061580701)
    ·
      refine ⟨6512505394776124898092763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17366681052736333061580701 6512505394776124898092763)
      ·
        refine ⟨9768758092164187347139145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512505394776124898092763 9768758092164187347139145)
        ·
          refine ⟨7326568569123140510354359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9768758092164187347139145 7326568569123140510354359)
          ·
            refine ⟨10989852853684710765531539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7326568569123140510354359 10989852853684710765531539)
            ·
              refine ⟨16484779280527066148297309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10989852853684710765531539 16484779280527066148297309)
              ·
                refine ⟨6181792230197649805611491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16484779280527066148297309 6181792230197649805611491)
                ·
                  refine ⟨9272688345296474708417237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181792230197649805611491 9272688345296474708417237)
                  ·
                    refine ⟨217328633092886125978529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9272688345296474708417237 217328633092886125978529)
                    ·
                      rfl

theorem cell23_1269738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1269738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269738 prefixEnd_1269738 := by exact prefixLift 1269738
  have htrace : WordTrace (prefixWord ++ tailWord_1269738) baseStart_1269738 baseEnd_1269738 := by
    simpa [prefixWord, tailWord_1269738, baseEnd_1269738] using wordTrace_append hprefix tailTrace_1269738
  have hstable : (prefixWord ++ tailWord_1269738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269738).length < 2 ^ (prefixWord ++ tailWord_1269738).sum := by decide
  have hdescent : baseEnd_1269738 < baseStart_1269738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269742 : List Nat := [4, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_1269742 : Nat := 118140960795 + 1269742 * 2 ^ 59
def prefixEnd_1269742 : Nat := 4983230072969 + 3 ^ 40 * 1269742 * 2
def baseEnd_1269742 : Nat := 72443105911252929142841

theorem tailTrace_1269742 : CollatzResearch.WordTrace tailWord_1269742 prefixEnd_1269742 72443105911252929142841 := by
  unfold tailWord_1269742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5788911920743632939253435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30874196910632709009351653 5788911920743632939253435)
  ·
    refine ⟨8683367881115449408880153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5788911920743632939253435 8683367881115449408880153)
    ·
      refine ⟨6512525910836587056660115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8683367881115449408880153 6512525910836587056660115)
      ·
        refine ⟨9768788866254880584990173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512525910836587056660115 9768788866254880584990173)
        ·
          refine ⟨3663295824845580219371315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9768788866254880584990173 3663295824845580219371315)
          ·
            refine ⟨5494943737268370329056973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663295824845580219371315 5494943737268370329056973)
            ·
              refine ⟨2060603901475638873396365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5494943737268370329056973 2060603901475638873396365)
              ·
                refine ⟨772726463053364577523637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2060603901475638873396365 772726463053364577523637)
                ·
                  refine ⟨72443105911252929142841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 772726463053364577523637 72443105911252929142841)
                  ·
                    rfl

theorem cell23_1269742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_1269742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269742 prefixEnd_1269742 := by exact prefixLift 1269742
  have htrace : WordTrace (prefixWord ++ tailWord_1269742) baseStart_1269742 baseEnd_1269742 := by
    simpa [prefixWord, tailWord_1269742, baseEnd_1269742] using wordTrace_append hprefix tailTrace_1269742
  have hstable : (prefixWord ++ tailWord_1269742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269742).length < 2 ^ (prefixWord ++ tailWord_1269742).sum := by decide
  have hdescent : baseEnd_1269742 < baseStart_1269742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269818 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1269818 : Nat := 118140960795 + 1269818 * 2 ^ 59
def prefixEnd_1269818 : Nat := 4983230072969 + 3 ^ 40 * 1269818 * 2
def baseEnd_1269818 : Nat := 652026977731018064935219

theorem tailTrace_1269818 : CollatzResearch.WordTrace tailWord_1269818 prefixEnd_1269818 652026977731018064935219 := by
  unfold tailWord_1269818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11578516828418432123448527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30876044875782485662529405 11578516828418432123448527)
  ·
    refine ⟨17367775242627648185172791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11578516828418432123448527 17367775242627648185172791)
    ·
      refine ⟨26051662863941472277759187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17367775242627648185172791 26051662863941472277759187)
      ·
        refine ⟨39077494295912208416638781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26051662863941472277759187 39077494295912208416638781)
        ·
          refine ⟨14654060360967078156239543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39077494295912208416638781 14654060360967078156239543)
          ·
            refine ⟨21981090541450617234359315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14654060360967078156239543 21981090541450617234359315)
            ·
              refine ⟨32971635812175925851538973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21981090541450617234359315 32971635812175925851538973)
              ·
                refine ⟨12364363429565972194327115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32971635812175925851538973 12364363429565972194327115)
                ·
                  refine ⟨18546545144348958291490673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12364363429565972194327115 18546545144348958291490673)
                  ·
                    refine ⟨13909908858261718718618005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18546545144348958291490673 13909908858261718718618005)
                    ·
                      refine ⟨652026977731018064935219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13909908858261718718618005 652026977731018064935219)
                      ·
                        rfl

theorem cell23_1269818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1269818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269818 prefixEnd_1269818 := by exact prefixLift 1269818
  have htrace : WordTrace (prefixWord ++ tailWord_1269818) baseStart_1269818 baseEnd_1269818 := by
    simpa [prefixWord, tailWord_1269818, baseEnd_1269818] using wordTrace_append hprefix tailTrace_1269818
  have hstable : (prefixWord ++ tailWord_1269818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269818).length < 2 ^ (prefixWord ++ tailWord_1269818).sum := by decide
  have hdescent : baseEnd_1269818 < baseStart_1269818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269835 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 3, 5, 2]
def baseStart_1269835 : Nat := 118140960795 + 1269835 * 2 ^ 59
def prefixEnd_1269835 : Nat := 4983230072969 + 3 ^ 40 * 1269835 * 2
def baseEnd_1269835 : Nat := 652035706902144498422641

theorem tailTrace_1269835 : CollatzResearch.WordTrace tailWord_1269835 prefixEnd_1269835 652035706902144498422641 := by
  unfold tailWord_1269835
  simp only [CollatzResearch.WordTrace]
  refine ⟨46314687354612140397162959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30876458236408093598108639 46314687354612140397162959)
  ·
    refine ⟨69472031031918210595744439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46314687354612140397162959 69472031031918210595744439)
    ·
      refine ⟨104208046547877315893616659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69472031031918210595744439 104208046547877315893616659)
      ·
        refine ⟨156312069821815973840424989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104208046547877315893616659 156312069821815973840424989)
        ·
          refine ⟨58617026183180990190159371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156312069821815973840424989 58617026183180990190159371)
          ·
            refine ⟨87925539274771485285239057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58617026183180990190159371 87925539274771485285239057)
            ·
              refine ⟨65944154456078613963929293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87925539274771485285239057 65944154456078613963929293)
              ·
                refine ⟨24729057921029480236473485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65944154456078613963929293 24729057921029480236473485)
                ·
                  refine ⟨9273396720386055088677557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24729057921029480236473485 9273396720386055088677557)
                  ·
                    refine ⟨869380942536192664563521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9273396720386055088677557 869380942536192664563521)
                    ·
                      refine ⟨652035706902144498422641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869380942536192664563521 652035706902144498422641)
                      ·
                        rfl

theorem cell23_1269835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5, 2].length) (baseStart_1269835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269835 prefixEnd_1269835 := by exact prefixLift 1269835
  have htrace : WordTrace (prefixWord ++ tailWord_1269835) baseStart_1269835 baseEnd_1269835 := by
    simpa [prefixWord, tailWord_1269835, baseEnd_1269835] using wordTrace_append hprefix tailTrace_1269835
  have hstable : (prefixWord ++ tailWord_1269835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269835).length < 2 ^ (prefixWord ++ tailWord_1269835).sum := by decide
  have hdescent : baseEnd_1269835 < baseStart_1269835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269845 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1269845 : Nat := 118140960795 + 1269845 * 2 ^ 59
def prefixEnd_1269845 : Nat := 4983230072969 + 3 ^ 40 * 1269845 * 2
def baseEnd_1269845 : Nat := 217346947236229819765865

theorem tailTrace_1269845 : CollatzResearch.WordTrace tailWord_1269845 prefixEnd_1269845 217346947236229819765865 := by
  unfold tailWord_1269845
  simp only [CollatzResearch.WordTrace]
  refine ⟨46315052084575912105026989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30876701389717274736684659 46315052084575912105026989)
  ·
    refine ⟨17368144531715967039385121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46315052084575912105026989 17368144531715967039385121)
    ·
      refine ⟨13026108398786975279538841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17368144531715967039385121 13026108398786975279538841)
      ·
        refine ⟨9769581299090231459654131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13026108398786975279538841 9769581299090231459654131)
        ·
          refine ⟨14654371948635347189481197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9769581299090231459654131 14654371948635347189481197)
          ·
            refine ⟨5495389480738255196055449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14654371948635347189481197 5495389480738255196055449)
            ·
              refine ⟨4121542110553691397041587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495389480738255196055449 4121542110553691397041587)
              ·
                refine ⟨6182313165830537095562381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121542110553691397041587 6182313165830537095562381)
                ·
                  refine ⟨2318367437186451410835893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6182313165830537095562381 2318367437186451410835893)
                  ·
                    refine ⟨217346947236229819765865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2318367437186451410835893 217346947236229819765865)
                    ·
                      rfl

theorem cell23_1269845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1269845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269845 prefixEnd_1269845 := by exact prefixLift 1269845
  have htrace : WordTrace (prefixWord ++ tailWord_1269845) baseStart_1269845 baseEnd_1269845 := by
    simpa [prefixWord, tailWord_1269845, baseEnd_1269845] using wordTrace_append hprefix tailTrace_1269845
  have hstable : (prefixWord ++ tailWord_1269845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269845).length < 2 ^ (prefixWord ++ tailWord_1269845).sum := by decide
  have hdescent : baseEnd_1269845 < baseStart_1269845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269846 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1269846 : Nat := 118140960795 + 1269846 * 2 ^ 59
def prefixEnd_1269846 : Nat := 4983230072969 + 3 ^ 40 * 1269846 * 2
def baseEnd_1269846 : Nat := 652041355189343955385091

theorem tailTrace_1269846 : CollatzResearch.WordTrace tailWord_1269846 prefixEnd_1269846 652041355189343955385091 := by
  unfold tailWord_1269846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894693034848268079738337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30876725705048192850542261 2894693034848268079738337)
  ·
    refine ⟨2171019776136201059803753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2894693034848268079738337 2171019776136201059803753)
    ·
      refine ⟨1628264832102150794852815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2171019776136201059803753 1628264832102150794852815)
      ·
        refine ⟨2442397248153226192279223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628264832102150794852815 2442397248153226192279223)
        ·
          refine ⟨3663595872229839288418835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442397248153226192279223 3663595872229839288418835)
          ·
            refine ⟨5495393808344758932628253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663595872229839288418835 5495393808344758932628253)
            ·
              refine ⟨2060772678129284599735595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5495393808344758932628253 2060772678129284599735595)
              ·
                refine ⟨3091159017193926899603393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060772678129284599735595 3091159017193926899603393)
                ·
                  refine ⟨2318369262895445174702545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091159017193926899603393 2318369262895445174702545)
                  ·
                    refine ⟨1738776947171583881026909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318369262895445174702545 1738776947171583881026909)
                    ·
                      refine ⟨652041355189343955385091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738776947171583881026909 652041355189343955385091)
                      ·
                        rfl

theorem cell23_1269846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1269846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269846 prefixEnd_1269846 := by exact prefixLift 1269846
  have htrace : WordTrace (prefixWord ++ tailWord_1269846) baseStart_1269846 baseEnd_1269846 := by
    simpa [prefixWord, tailWord_1269846, baseEnd_1269846] using wordTrace_append hprefix tailTrace_1269846
  have hstable : (prefixWord ++ tailWord_1269846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269846).length < 2 ^ (prefixWord ++ tailWord_1269846).sum := by decide
  have hdescent : baseEnd_1269846 < baseStart_1269846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269859 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 1, 1, 3]
def baseStart_1269859 : Nat := 118140960795 + 1269859 * 2 ^ 59
def prefixEnd_1269859 : Nat := 4983230072969 + 3 ^ 40 * 1269859 * 2
def baseEnd_1269859 : Nat := 652048030437852404522531

theorem tailTrace_1269859 : CollatzResearch.WordTrace tailWord_1269859 prefixEnd_1269859 652048030437852404522531 := by
  unfold tailWord_1269859
  simp only [CollatzResearch.WordTrace]
  refine ⟨46315562706525192496036631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30877041804350128330691087 46315562706525192496036631)
  ·
    refine ⟨69473344059787788744054947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46315562706525192496036631 69473344059787788744054947)
    ·
      refine ⟨104210016089681683116082421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69473344059787788744054947 104210016089681683116082421)
      ·
        refine ⟨9769689008407657792132727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104210016089681683116082421 9769689008407657792132727)
        ·
          refine ⟨14654533512611486688199091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9769689008407657792132727 14654533512611486688199091)
          ·
            refine ⟨21981800268917230032298637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14654533512611486688199091 21981800268917230032298637)
            ·
              refine ⟨8243175100843961262111989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21981800268917230032298637 8243175100843961262111989)
              ·
                refine ⟨772797665704121368322999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8243175100843961262111989 772797665704121368322999)
                ·
                  refine ⟨1159196498556182052484499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772797665704121368322999 1159196498556182052484499)
                  ·
                    refine ⟨1738794747834273078726749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1159196498556182052484499 1738794747834273078726749)
                    ·
                      refine ⟨652048030437852404522531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738794747834273078726749 652048030437852404522531)
                      ·
                        rfl

theorem cell23_1269859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_1269859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269859 prefixEnd_1269859 := by exact prefixLift 1269859
  have htrace : WordTrace (prefixWord ++ tailWord_1269859) baseStart_1269859 baseEnd_1269859 := by
    simpa [prefixWord, tailWord_1269859, baseEnd_1269859] using wordTrace_append hprefix tailTrace_1269859
  have hstable : (prefixWord ++ tailWord_1269859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269859).length < 2 ^ (prefixWord ++ tailWord_1269859).sum := by decide
  have hdescent : baseEnd_1269859 < baseStart_1269859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269885 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1269885 : Nat := 118140960795 + 1269885 * 2 ^ 59
def prefixEnd_1269885 : Nat := 4983230072969 + 3 ^ 40 * 1269885 * 2
def baseEnd_1269885 : Nat := 652061380934869302797411

theorem tailTrace_1269885 : CollatzResearch.WordTrace tailWord_1269885 prefixEnd_1269885 652061380934869302797411 := by
  unfold tailWord_1269885
  simp only [CollatzResearch.WordTrace]
  refine ⟨46316511004430998936483109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30877674002953999290988739 46316511004430998936483109)
  ·
    refine ⟨8684345813330812300590583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46316511004430998936483109 8684345813330812300590583)
    ·
      refine ⟨13026518719996218450885875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8684345813330812300590583 13026518719996218450885875)
      ·
        refine ⟨19539778079994327676328813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13026518719996218450885875 19539778079994327676328813)
        ·
          refine ⟨7327416779997872878623305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19539778079994327676328813 7327416779997872878623305)
          ·
            refine ⟨5495562584998404658967479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7327416779997872878623305 5495562584998404658967479)
            ·
              refine ⟨8243343877497606988451219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495562584998404658967479 8243343877497606988451219)
              ·
                refine ⟨12365015816246410482676829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8243343877497606988451219 12365015816246410482676829)
                ·
                  refine ⟨4636880931092403931003811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12365015816246410482676829 4636880931092403931003811)
                  ·
                    refine ⟨6955321396638605896505717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4636880931092403931003811 6955321396638605896505717)
                    ·
                      refine ⟨652061380934869302797411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6955321396638605896505717 652061380934869302797411)
                      ·
                        rfl

theorem cell23_1269885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1269885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269885 prefixEnd_1269885 := by exact prefixLift 1269885
  have htrace : WordTrace (prefixWord ++ tailWord_1269885) baseStart_1269885 baseEnd_1269885 := by
    simpa [prefixWord, tailWord_1269885, baseEnd_1269885] using wordTrace_append hprefix tailTrace_1269885
  have hstable : (prefixWord ++ tailWord_1269885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269885).length < 2 ^ (prefixWord ++ tailWord_1269885).sum := by decide
  have hdescent : baseEnd_1269885 < baseStart_1269885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269888 : List Nat := [2, 1, 1, 2, 1, 3, 1, 12]
def baseStart_1269888 : Nat := 118140960795 + 1269888 * 2 ^ 59
def prefixEnd_1269888 : Nat := 4983230072969 + 3 ^ 40 * 1269888 * 2
def baseEnd_1269888 : Nat := 24150478569512325594811

theorem tailTrace_1269888 : CollatzResearch.WordTrace tailWord_1269888 prefixEnd_1269888 24150478569512325594811 := by
  unfold tailWord_1269888
  simp only [CollatzResearch.WordTrace]
  refine ⟨23158310211710065224421159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30877746948946753632561545 23158310211710065224421159)
  ·
    refine ⟨34737465317565097836631739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23158310211710065224421159 34737465317565097836631739)
    ·
      refine ⟨52106197976347646754947609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34737465317565097836631739 52106197976347646754947609)
      ·
        refine ⟨39079648482260735066210707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52106197976347646754947609 39079648482260735066210707)
        ·
          refine ⟨58619472723391102599316061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39079648482260735066210707 58619472723391102599316061)
          ·
            refine ⟨21982302271271663474743523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58619472723391102599316061 21982302271271663474743523)
            ·
              refine ⟨32973453406907495212115285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21982302271271663474743523 32973453406907495212115285)
              ·
                refine ⟨24150478569512325594811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 32973453406907495212115285 24150478569512325594811)
                ·
                  rfl

theorem cell23_1269888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 12].length) (baseStart_1269888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269888 prefixEnd_1269888 := by exact prefixLift 1269888
  have htrace : WordTrace (prefixWord ++ tailWord_1269888) baseStart_1269888 baseEnd_1269888 := by
    simpa [prefixWord, tailWord_1269888, baseEnd_1269888] using wordTrace_append hprefix tailTrace_1269888
  have hstable : (prefixWord ++ tailWord_1269888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269888).length < 2 ^ (prefixWord ++ tailWord_1269888).sum := by decide
  have hdescent : baseEnd_1269888 < baseStart_1269888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269919 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1269919 : Nat := 118140960795 + 1269919 * 2 ^ 59
def prefixEnd_1269919 : Nat := 4983230072969 + 3 ^ 40 * 1269919 * 2
def baseEnd_1269919 : Nat := 652078839277122169772255

theorem tailTrace_1269919 : CollatzResearch.WordTrace tailWord_1269919 prefixEnd_1269919 652078839277122169772255 := by
  unfold tailWord_1269919
  simp only [CollatzResearch.WordTrace]
  refine ⟨46317751086307822743220811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30878500724205215162147207 46317751086307822743220811)
  ·
    refine ⟨69476626629461734114831217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46317751086307822743220811 69476626629461734114831217)
    ·
      refine ⟨52107469972096300586123413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69476626629461734114831217 52107469972096300586123413)
      ·
        refine ⟨2442537654942014089974535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52107469972096300586123413 2442537654942014089974535)
        ·
          refine ⟨3663806482413021134961803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442537654942014089974535 3663806482413021134961803)
          ·
            refine ⟨5495709723619531702442705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663806482413021134961803 5495709723619531702442705)
            ·
              refine ⟨4121782292714648776832029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495709723619531702442705 4121782292714648776832029)
              ·
                refine ⟨1545668359767993291312011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4121782292714648776832029 1545668359767993291312011)
                ·
                  refine ⟨2318502539651989936968017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545668359767993291312011 2318502539651989936968017)
                  ·
                    refine ⟨1738876904738992452726013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318502539651989936968017 1738876904738992452726013)
                    ·
                      refine ⟨652078839277122169772255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738876904738992452726013 652078839277122169772255)
                      ·
                        rfl

theorem cell23_1269919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1269919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269919 prefixEnd_1269919 := by exact prefixLift 1269919
  have htrace : WordTrace (prefixWord ++ tailWord_1269919) baseStart_1269919 baseEnd_1269919 := by
    simpa [prefixWord, tailWord_1269919, baseEnd_1269919] using wordTrace_append hprefix tailTrace_1269919
  have hstable : (prefixWord ++ tailWord_1269919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269919).length < 2 ^ (prefixWord ++ tailWord_1269919).sum := by decide
  have hdescent : baseEnd_1269919 < baseStart_1269919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269922 : List Nat := [3, 3, 1, 3, 1, 3, 9]
def baseStart_1269922 : Nat := 118140960795 + 1269922 * 2 ^ 59
def prefixEnd_1269922 : Nat := 4983230072969 + 3 ^ 40 * 1269922 * 2
def baseEnd_1269922 : Nat := 8050375058260316765861

theorem tailTrace_1269922 : CollatzResearch.WordTrace tailWord_1269922 prefixEnd_1269922 8050375058260316765861 := by
  unfold tailWord_1269922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579465126324238563895005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30878573670197969503720013 11579465126324238563895005)
  ·
    refine ⟨4342299422371589461460627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11579465126324238563895005 4342299422371589461460627)
    ·
      refine ⟨6513449133557384192190941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342299422371589461460627 6513449133557384192190941)
      ·
        refine ⟨2442543425084019072071603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6513449133557384192190941 2442543425084019072071603)
        ·
          refine ⟨3663815137626028608107405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442543425084019072071603 3663815137626028608107405)
          ·
            refine ⟨1373930676609760728040277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3663815137626028608107405 1373930676609760728040277)
            ·
              refine ⟨8050375058260316765861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1373930676609760728040277 8050375058260316765861)
              ·
                rfl

theorem cell23_1269922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 9].length) (baseStart_1269922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269922 prefixEnd_1269922 := by exact prefixLift 1269922
  have htrace : WordTrace (prefixWord ++ tailWord_1269922) baseStart_1269922 baseEnd_1269922 := by
    simpa [prefixWord, tailWord_1269922, baseEnd_1269922] using wordTrace_append hprefix tailTrace_1269922
  have hstable : (prefixWord ++ tailWord_1269922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269922).length < 2 ^ (prefixWord ++ tailWord_1269922).sum := by decide
  have hdescent : baseEnd_1269922 < baseStart_1269922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269933 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_1269933 : Nat := 118140960795 + 1269933 * 2 ^ 59
def prefixEnd_1269933 : Nat := 4983230072969 + 3 ^ 40 * 1269933 * 2
def baseEnd_1269933 : Nat := 652086028006285114997191

theorem tailTrace_1269933 : CollatzResearch.WordTrace tailWord_1269933 prefixEnd_1269933 652086028006285114997191 := by
  unfold tailWord_1269933
  simp only [CollatzResearch.WordTrace]
  refine ⟨46318261708257103134230453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30878841138838068756153635 46318261708257103134230453)
  ·
    refine ⟨4342337035149103418834105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46318261708257103134230453 4342337035149103418834105)
    ·
      refine ⟨3256752776361827564125579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4342337035149103418834105 3256752776361827564125579)
      ·
        refine ⟨4885129164542741346188369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256752776361827564125579 4885129164542741346188369)
        ·
          refine ⟨3663846873407056009641277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885129164542741346188369 3663846873407056009641277)
          ·
            refine ⟨1373942577527646003615479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3663846873407056009641277 1373942577527646003615479)
            ·
              refine ⟨2060913866291469005423219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373942577527646003615479 2060913866291469005423219)
              ·
                refine ⟨3091370799437203508134829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060913866291469005423219 3091370799437203508134829)
                ·
                  refine ⟨1159264049788951315550561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3091370799437203508134829 1159264049788951315550561)
                  ·
                    refine ⟨869448037341713486662921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1159264049788951315550561 869448037341713486662921)
                    ·
                      refine ⟨652086028006285114997191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869448037341713486662921 652086028006285114997191)
                      ·
                        rfl

theorem cell23_1269933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_1269933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269933 prefixEnd_1269933 := by exact prefixLift 1269933
  have htrace : WordTrace (prefixWord ++ tailWord_1269933) baseStart_1269933 baseEnd_1269933 := by
    simpa [prefixWord, tailWord_1269933, baseEnd_1269933] using wordTrace_append hprefix tailTrace_1269933
  have hstable : (prefixWord ++ tailWord_1269933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269933).length < 2 ^ (prefixWord ++ tailWord_1269933).sum := by decide
  have hdescent : baseEnd_1269933 < baseStart_1269933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269953 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1269953 : Nat := 118140960795 + 1269953 * 2 ^ 59
def prefixEnd_1269953 : Nat := 4983230072969 + 3 ^ 40 * 1269953 * 2
def baseEnd_1269953 : Nat := 652096297619375036747099

theorem tailTrace_1269953 : CollatzResearch.WordTrace tailWord_1269953 prefixEnd_1269953 652096297619375036747099 := by
  unfold tailWord_1269953
  simp only [CollatzResearch.WordTrace]
  refine ⟨46318991168184646549958513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30879327445456431033305675 46318991168184646549958513)
  ·
    refine ⟨34739243376138484912468885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46318991168184646549958513 34739243376138484912468885)
    ·
      refine ⟨1628402033256491480271979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34739243376138484912468885 1628402033256491480271979)
      ·
        refine ⟨2442603049884737220407969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628402033256491480271979 2442603049884737220407969)
        ·
          refine ⟨1831952287413552915305977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2442603049884737220407969 1831952287413552915305977)
          ·
            refine ⟨1373964215560164686479483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1831952287413552915305977 1373964215560164686479483)
            ·
              refine ⟨2060946323340247029719225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373964215560164686479483 2060946323340247029719225)
              ·
                refine ⟨1545709742505185272289419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060946323340247029719225 1545709742505185272289419)
                ·
                  refine ⟨2318564613757777908434129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545709742505185272289419 2318564613757777908434129)
                  ·
                    refine ⟨1738923460318333431325597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318564613757777908434129 1738923460318333431325597)
                    ·
                      refine ⟨652096297619375036747099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738923460318333431325597 652096297619375036747099)
                      ·
                        rfl

theorem cell23_1269953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1269953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269953 prefixEnd_1269953 := by exact prefixLift 1269953
  have htrace : WordTrace (prefixWord ++ tailWord_1269953) baseStart_1269953 baseEnd_1269953 := by
    simpa [prefixWord, tailWord_1269953, baseEnd_1269953] using wordTrace_append hprefix tailTrace_1269953
  have hstable : (prefixWord ++ tailWord_1269953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269953).length < 2 ^ (prefixWord ++ tailWord_1269953).sum := by decide
  have hdescent : baseEnd_1269953 < baseStart_1269953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269992 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1269992 : Nat := 118140960795 + 1269992 * 2 ^ 59
def prefixEnd_1269992 : Nat := 4983230072969 + 3 ^ 40 * 1269992 * 2
def baseEnd_1269992 : Nat := 652116323364900384159419

theorem tailTrace_1269992 : CollatzResearch.WordTrace tailWord_1269992 prefixEnd_1269992 652116323364900384159419 := by
  unfold tailWord_1269992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23160206807521678105314115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30880275743362237473752153 23160206807521678105314115)
  ·
    refine ⟨34740310211282517157971173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23160206807521678105314115 34740310211282517157971173)
    ·
      refine ⟨6513808164615471967119595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34740310211282517157971173 6513808164615471967119595)
      ·
        refine ⟨9770712246923207950679393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6513808164615471967119595 9770712246923207950679393)
        ·
          refine ⟨7328034185192405963009545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9770712246923207950679393 7328034185192405963009545)
          ·
            refine ⟨5496025638894304472257159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7328034185192405963009545 5496025638894304472257159)
            ·
              refine ⟨8244038458341456708385739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496025638894304472257159 8244038458341456708385739)
              ·
                refine ⟨12366057687512185062578609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8244038458341456708385739 12366057687512185062578609)
                ·
                  refine ⟨9274543265634138796933957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12366057687512185062578609 9274543265634138796933957)
                  ·
                    refine ⟨1738976862306401024425117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9274543265634138796933957 1738976862306401024425117)
                    ·
                      refine ⟨652116323364900384159419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1738976862306401024425117 652116323364900384159419)
                      ·
                        rfl

theorem cell23_1269992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1269992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269992 prefixEnd_1269992 := by exact prefixLift 1269992
  have htrace : WordTrace (prefixWord ++ tailWord_1269992) baseStart_1269992 baseEnd_1269992 := by
    simpa [prefixWord, tailWord_1269992, baseEnd_1269992] using wordTrace_append hprefix tailTrace_1269992
  have hstable : (prefixWord ++ tailWord_1269992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269992).length < 2 ^ (prefixWord ++ tailWord_1269992).sum := by decide
  have hdescent : baseEnd_1269992 < baseStart_1269992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1269995 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 7]
def baseStart_1269995 : Nat := 118140960795 + 1269995 * 2 ^ 59
def prefixEnd_1269995 : Nat := 4983230072969 + 3 ^ 40 * 1269995 * 2
def baseEnd_1269995 : Nat := 72457540422984874713545

theorem tailTrace_1269995 : CollatzResearch.WordTrace tailWord_1269995 prefixEnd_1269995 72457540422984874713545 := by
  unfold tailWord_1269995
  simp only [CollatzResearch.WordTrace]
  refine ⟨46320523034032487722987439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30880348689354991815324959 46320523034032487722987439)
  ·
    refine ⟨69480784551048731584481159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46320523034032487722987439 69480784551048731584481159)
    ·
      refine ⟨104221176826573097376721739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69480784551048731584481159 104221176826573097376721739)
      ·
        refine ⟨156331765239859646065082609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104221176826573097376721739 156331765239859646065082609)
        ·
          refine ⟨117248823929894734548811957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156331765239859646065082609 117248823929894734548811957)
          ·
            refine ⟨10992077243427631363951121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117248823929894734548811957 10992077243427631363951121)
            ·
              refine ⟨8244057932570723522963341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10992077243427631363951121 8244057932570723522963341)
              ·
                refine ⟨3091521724714021321111253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8244057932570723522963341 3091521724714021321111253)
                ·
                  refine ⟨72457540422984874713545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3091521724714021321111253 72457540422984874713545)
                  ·
                    rfl

theorem cell23_1269995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 7].length) (baseStart_1269995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1269995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1269995 prefixEnd_1269995 := by exact prefixLift 1269995
  have htrace : WordTrace (prefixWord ++ tailWord_1269995) baseStart_1269995 baseEnd_1269995 := by
    simpa [prefixWord, tailWord_1269995, baseEnd_1269995] using wordTrace_append hprefix tailTrace_1269995
  have hstable : (prefixWord ++ tailWord_1269995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1269995).length < 2 ^ (prefixWord ++ tailWord_1269995).sum := by decide
  have hdescent : baseEnd_1269995 < baseStart_1269995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1269995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270002 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1270002 : Nat := 118140960795 + 1270002 * 2 ^ 59
def prefixEnd_1270002 : Nat := 4983230072969 + 3 ^ 40 * 1270002 * 2
def baseEnd_1270002 : Nat := 652121458171445345034373

theorem tailTrace_1270002 : CollatzResearch.WordTrace tailWord_1270002 prefixEnd_1270002 652121458171445345034373 := by
  unfold tailWord_1270002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580194586251781979623065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30880518896671418612328173 11580194586251781979623065)
  ·
    refine ⟨8685145939688836484717299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11580194586251781979623065 8685145939688836484717299)
    ·
      refine ⟨13027718909533254727075949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8685145939688836484717299 13027718909533254727075949)
      ·
        refine ⟨4885394591074970522653481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13027718909533254727075949 4885394591074970522653481)
        ·
          refine ⟨3664045943306227891990111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885394591074970522653481 3664045943306227891990111)
          ·
            refine ⟨5496068914959341837985167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664045943306227891990111 5496068914959341837985167)
            ·
              refine ⟨8244103372439012756977751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496068914959341837985167 8244103372439012756977751)
              ·
                refine ⟨12366155058658519135466627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8244103372439012756977751 12366155058658519135466627)
                ·
                  refine ⟨18549232587987778703199941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12366155058658519135466627 18549232587987778703199941)
                  ·
                    refine ⟨3477981110247708506849989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18549232587987778703199941 3477981110247708506849989)
                    ·
                      refine ⟨652121458171445345034373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3477981110247708506849989 652121458171445345034373)
                      ·
                        rfl

theorem cell23_1270002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1270002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270002 prefixEnd_1270002 := by exact prefixLift 1270002
  have htrace : WordTrace (prefixWord ++ tailWord_1270002) baseStart_1270002 baseEnd_1270002 := by
    simpa [prefixWord, tailWord_1270002, baseEnd_1270002] using wordTrace_append hprefix tailTrace_1270002
  have hstable : (prefixWord ++ tailWord_1270002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270002).length < 2 ^ (prefixWord ++ tailWord_1270002).sum := by decide
  have hdescent : baseEnd_1270002 < baseStart_1270002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270012 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 7]
def baseStart_1270012 : Nat := 118140960795 + 1270012 * 2 ^ 59
def prefixEnd_1270012 : Nat := 4983230072969 + 3 ^ 40 * 1270012 * 2
def baseEnd_1270012 : Nat := 72458510330887811767703

theorem tailTrace_1270012 : CollatzResearch.WordTrace tailWord_1270012 prefixEnd_1270012 72458510330887811767703 := by
  unfold tailWord_1270012
  simp only [CollatzResearch.WordTrace]
  refine ⟨23160571537485449813178145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30880762049980599750904193 23160571537485449813178145)
  ·
    refine ⟨17370428653114087359883609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23160571537485449813178145 17370428653114087359883609)
    ·
      refine ⟨13027821489835565519912707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17370428653114087359883609 13027821489835565519912707)
      ·
        refine ⟨19541732234753348279869061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13027821489835565519912707 19541732234753348279869061)
        ·
          refine ⟨3664074794016252802475449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19541732234753348279869061 3664074794016252802475449)
          ·
            refine ⟨2748056095512189601856587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3664074794016252802475449 2748056095512189601856587)
            ·
              refine ⟨4122084143268284402784881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748056095512189601856587 4122084143268284402784881)
              ·
                refine ⟨3091563107451213302088661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122084143268284402784881 3091563107451213302088661)
                ·
                  refine ⟨72458510330887811767703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3091563107451213302088661 72458510330887811767703)
                  ·
                    rfl

theorem cell23_1270012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_1270012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270012 prefixEnd_1270012 := by exact prefixLift 1270012
  have htrace : WordTrace (prefixWord ++ tailWord_1270012) baseStart_1270012 baseEnd_1270012 := by
    simpa [prefixWord, tailWord_1270012, baseEnd_1270012] using wordTrace_append hprefix tailTrace_1270012
  have hstable : (prefixWord ++ tailWord_1270012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270012).length < 2 ^ (prefixWord ++ tailWord_1270012).sum := by decide
  have hdescent : baseEnd_1270012 < baseStart_1270012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270035 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_1270035 : Nat := 118140960795 + 1270035 * 2 ^ 59
def prefixEnd_1270035 : Nat := 4983230072969 + 3 ^ 40 * 1270035 * 2
def baseEnd_1270035 : Nat := 652138403033043715921721

theorem tailTrace_1270035 : CollatzResearch.WordTrace tailWord_1270035 prefixEnd_1270035 652138403033043715921721 := by
  unfold tailWord_1270035
  simp only [CollatzResearch.WordTrace]
  refine ⟨46321981953887574554443559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30881321302591716369629039 46321981953887574554443559)
  ·
    refine ⟨69482972930831361831665339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46321981953887574554443559 69482972930831361831665339)
    ·
      refine ⟨104224459396247042747498009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69482972930831361831665339 104224459396247042747498009)
      ·
        refine ⟨78168344547185282060623507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104224459396247042747498009 78168344547185282060623507)
        ·
          refine ⟨117252516820777923090935261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78168344547185282060623507 117252516820777923090935261)
          ·
            refine ⟨43969693807791721159100723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117252516820777923090935261 43969693807791721159100723)
            ·
              refine ⟨65954540711687581738651085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43969693807791721159100723 65954540711687581738651085)
              ·
                refine ⟨24732952766882843151994157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65954540711687581738651085 24732952766882843151994157)
                ·
                  refine ⟨9274857287581066181997809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24732952766882843151994157 9274857287581066181997809)
                  ·
                    refine ⟨6956142965685799636498357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9274857287581066181997809 6956142965685799636498357)
                    ·
                      refine ⟨652138403033043715921721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6956142965685799636498357 652138403033043715921721)
                      ·
                        rfl

theorem cell23_1270035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_1270035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270035 prefixEnd_1270035 := by exact prefixLift 1270035
  have htrace : WordTrace (prefixWord ++ tailWord_1270035) baseStart_1270035 baseEnd_1270035 := by
    simpa [prefixWord, tailWord_1270035, baseEnd_1270035] using wordTrace_append hprefix tailTrace_1270035
  have hstable : (prefixWord ++ tailWord_1270035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270035).length < 2 ^ (prefixWord ++ tailWord_1270035).sum := by decide
  have hdescent : baseEnd_1270035 < baseStart_1270035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270046 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1270046 : Nat := 118140960795 + 1270046 * 2 ^ 59
def prefixEnd_1270046 : Nat := 4983230072969 + 3 ^ 40 * 1270046 * 2
def baseEnd_1270046 : Nat := 72460450146693685876019

theorem tailTrace_1270046 : CollatzResearch.WordTrace tailWord_1270046 prefixEnd_1270046 72460450146693685876019 := by
  unfold tailWord_1270046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5790297894605965429136749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30881588771231815622062661 5790297894605965429136749)
  ·
    refine ⟨2171361710477237035926281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5790297894605965429136749 2171361710477237035926281)
    ·
      refine ⟨1628521282857927776944711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2171361710477237035926281 1628521282857927776944711)
      ·
        refine ⟨2442781924286891665417067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628521282857927776944711 2442781924286891665417067)
        ·
          refine ⟨3664172886430337498125601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442781924286891665417067 3664172886430337498125601)
          ·
            refine ⟨2748129664822753123594201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3664172886430337498125601 2748129664822753123594201)
            ·
              refine ⟨2061097248617064842695651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748129664822753123594201 2061097248617064842695651)
              ·
                refine ⟨3091645872925597264043477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061097248617064842695651 3091645872925597264043477)
                ·
                  refine ⟨72460450146693685876019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3091645872925597264043477 72460450146693685876019)
                  ·
                    rfl

theorem cell23_1270046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1270046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270046 prefixEnd_1270046 := by exact prefixLift 1270046
  have htrace : WordTrace (prefixWord ++ tailWord_1270046) baseStart_1270046 baseEnd_1270046 := by
    simpa [prefixWord, tailWord_1270046, baseEnd_1270046] using wordTrace_append hprefix tailTrace_1270046
  have hstable : (prefixWord ++ tailWord_1270046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270046).length < 2 ^ (prefixWord ++ tailWord_1270046).sum := by decide
  have hdescent : baseEnd_1270046 < baseStart_1270046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270119 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 6]
def baseStart_1270119 : Nat := 118140960795 + 1270119 * 2 ^ 59
def prefixEnd_1270119 : Nat := 4983230072969 + 3 ^ 40 * 1270119 * 2
def baseEnd_1270119 : Nat := 72464615045335709696815

theorem tailTrace_1270119 : CollatzResearch.WordTrace tailWord_1270119 prefixEnd_1270119 72464615045335709696815 := by
  unfold tailWord_1270119
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325045685583256900501411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30883363790388837933667607 46325045685583256900501411)
  ·
    refine ⟨69487568528374885350752117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46325045685583256900501411 69487568528374885350752117)
    ·
      refine ⟨6514459549535145501633011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69487568528374885350752117 6514459549535145501633011)
      ·
        refine ⟨9771689324302718252449517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514459549535145501633011 9771689324302718252449517)
        ·
          refine ⟨3664383496613519344668569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9771689324302718252449517 3664383496613519344668569)
          ·
            refine ⟨2748287622460139508501427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3664383496613519344668569 2748287622460139508501427)
            ·
              refine ⟨4122431433690209262752141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748287622460139508501427 4122431433690209262752141)
              ·
                refine ⟨1545911787633828473532053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4122431433690209262752141 1545911787633828473532053)
                ·
                  refine ⟨72464615045335709696815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1545911787633828473532053 72464615045335709696815)
                  ·
                    rfl

theorem cell23_1270119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 6].length) (baseStart_1270119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270119 prefixEnd_1270119 := by exact prefixLift 1270119
  have htrace : WordTrace (prefixWord ++ tailWord_1270119) baseStart_1270119 baseEnd_1270119 := by
    simpa [prefixWord, tailWord_1270119, baseEnd_1270119] using wordTrace_append hprefix tailTrace_1270119
  have hstable : (prefixWord ++ tailWord_1270119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270119).length < 2 ^ (prefixWord ++ tailWord_1270119).sum := by decide
  have hdescent : baseEnd_1270119 < baseStart_1270119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270129 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_1270129 : Nat := 118140960795 + 1270129 * 2 ^ 59
def prefixEnd_1270129 : Nat := 4983230072969 + 3 ^ 40 * 1270129 * 2
def baseEnd_1270129 : Nat := 652186670214566348146289

theorem tailTrace_1270129 : CollatzResearch.WordTrace tailWord_1270129 prefixEnd_1270129 652186670214566348146289 := by
  unfold tailWord_1270129
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325410415547028608365441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30883606943698019072243627 46325410415547028608365441)
  ·
    refine ⟨34744057811660271456274081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46325410415547028608365441 34744057811660271456274081)
    ·
      refine ⟨26058043358745203592205561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34744057811660271456274081 26058043358745203592205561)
      ·
        refine ⟨19543532519058902694154171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26058043358745203592205561 19543532519058902694154171)
        ·
          refine ⟨29315298778588354041231257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19543532519058902694154171 29315298778588354041231257)
          ·
            refine ⟨21986474083941265530923443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29315298778588354041231257 21986474083941265530923443)
            ·
              refine ⟨32979711125911898296385165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21986474083941265530923443 32979711125911898296385165)
              ·
                refine ⟨12367391672216961861144437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32979711125911898296385165 12367391672216961861144437)
                ·
                  refine ⟨1159442969270340174482291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12367391672216961861144437 1159442969270340174482291)
                  ·
                    refine ⟨1739164453905510261723437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1159442969270340174482291 1739164453905510261723437)
                    ·
                      refine ⟨652186670214566348146289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1739164453905510261723437 652186670214566348146289)
                      ·
                        rfl

theorem cell23_1270129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_1270129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270129 prefixEnd_1270129 := by exact prefixLift 1270129
  have htrace : WordTrace (prefixWord ++ tailWord_1270129) baseStart_1270129 baseEnd_1270129 := by
    simpa [prefixWord, tailWord_1270129, baseEnd_1270129] using wordTrace_append hprefix tailTrace_1270129
  have hstable : (prefixWord ++ tailWord_1270129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270129).length < 2 ^ (prefixWord ++ tailWord_1270129).sum := by decide
  have hdescent : baseEnd_1270129 < baseStart_1270129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270156 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 2, 3, 2]
def baseStart_1270156 : Nat := 118140960795 + 1270156 * 2 ^ 59
def prefixEnd_1270156 : Nat := 4983230072969 + 3 ^ 40 * 1270156 * 2
def baseEnd_1270156 : Nat := 652200534192237742508665

theorem tailTrace_1270156 : CollatzResearch.WordTrace tailWord_1270156 prefixEnd_1270156 652200534192237742508665 := by
  unfold tailWord_1270156
  simp only [CollatzResearch.WordTrace]
  refine ⟨23163197593224606109799161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30884263457632808146398881 23163197593224606109799161)
  ·
    refine ⟨17372398194918454582349371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23163197593224606109799161 17372398194918454582349371)
    ·
      refine ⟨26058597292377681873524057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17372398194918454582349371 26058597292377681873524057)
      ·
        refine ⟨19543947969283261405143043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26058597292377681873524057 19543947969283261405143043)
        ·
          refine ⟨29315921953924892107714565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19543947969283261405143043 29315921953924892107714565)
          ·
            refine ⟨5496735366360917270196481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29315921953924892107714565 5496735366360917270196481)
            ·
              refine ⟨4122551524770687952647361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496735366360917270196481 4122551524770687952647361)
              ·
                refine ⟨3091913643578015964485521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122551524770687952647361 3091913643578015964485521)
                ·
                  refine ⟨2318935232683511973364141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091913643578015964485521 2318935232683511973364141)
                  ·
                    refine ⟨869600712256316990011553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318935232683511973364141 869600712256316990011553)
                    ·
                      refine ⟨652200534192237742508665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869600712256316990011553 652200534192237742508665)
                      ·
                        rfl

theorem cell23_1270156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_1270156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270156 prefixEnd_1270156 := by exact prefixLift 1270156
  have htrace : WordTrace (prefixWord ++ tailWord_1270156) baseStart_1270156 baseEnd_1270156 := by
    simpa [prefixWord, tailWord_1270156, baseEnd_1270156] using wordTrace_append hprefix tailTrace_1270156
  have hstable : (prefixWord ++ tailWord_1270156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270156).length < 2 ^ (prefixWord ++ tailWord_1270156).sum := by decide
  have hdescent : baseEnd_1270156 < baseStart_1270156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270179 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 1, 6]
def baseStart_1270179 : Nat := 118140960795 + 1270179 * 2 ^ 59
def prefixEnd_1270179 : Nat := 4983230072969 + 3 ^ 40 * 1270179 * 2
def baseEnd_1270179 : Nat := 217404114749097050840353

theorem tailTrace_1270179 : CollatzResearch.WordTrace tailWord_1270179 prefixEnd_1270179 217404114749097050840353 := by
  unfold tailWord_1270179
  simp only [CollatzResearch.WordTrace]
  refine ⟨46327234065365887147685591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30884822710243924765123727 46327234065365887147685591)
  ·
    refine ⟨69490851098048830721528387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46327234065365887147685591 69490851098048830721528387)
    ·
      refine ⟨104236276647073246082292581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69490851098048830721528387 104236276647073246082292581)
      ·
        refine ⟨19544301871326233640429859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104236276647073246082292581 19544301871326233640429859)
        ·
          refine ⟨29316452806989350460644789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19544301871326233640429859 29316452806989350460644789)
          ·
            refine ⟨2748417450655251605685449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29316452806989350460644789 2748417450655251605685449)
            ·
              refine ⟨2061313087991438704264087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748417450655251605685449 2061313087991438704264087)
              ·
                refine ⟨3091969631987158056396131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061313087991438704264087 3091969631987158056396131)
                ·
                  refine ⟨4637954447980737084594197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091969631987158056396131 4637954447980737084594197)
                  ·
                    refine ⟨217404114749097050840353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4637954447980737084594197 217404114749097050840353)
                    ·
                      rfl

theorem cell23_1270179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 6].length) (baseStart_1270179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270179 prefixEnd_1270179 := by exact prefixLift 1270179
  have htrace : WordTrace (prefixWord ++ tailWord_1270179) baseStart_1270179 baseEnd_1270179 := by
    simpa [prefixWord, tailWord_1270179, baseEnd_1270179] using wordTrace_append hprefix tailTrace_1270179
  have hstable : (prefixWord ++ tailWord_1270179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270179).length < 2 ^ (prefixWord ++ tailWord_1270179).sum := by decide
  have hdescent : baseEnd_1270179 < baseStart_1270179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270199 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 4]
def baseStart_1270199 : Nat := 118140960795 + 1270199 * 2 ^ 59
def prefixEnd_1270199 : Nat := 4983230072969 + 3 ^ 40 * 1270199 * 2
def baseEnd_1270199 : Nat := 652222613860381074270967

theorem tailTrace_1270199 : CollatzResearch.WordTrace tailWord_1270199 prefixEnd_1270199 652222613860381074270967 := by
  unfold tailWord_1270199
  simp only [CollatzResearch.WordTrace]
  refine ⟨46327963525293430563413651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30885309016862287042275767 46327963525293430563413651)
  ·
    refine ⟨69491945287940145845120477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46327963525293430563413651 69491945287940145845120477)
    ·
      refine ⟨26059479482977554691920179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69491945287940145845120477 26059479482977554691920179)
      ·
        refine ⟨39089219224466332037880269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26059479482977554691920179 39089219224466332037880269)
        ·
          refine ⟨14658457209174874514205101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39089219224466332037880269 14658457209174874514205101)
          ·
            refine ⟨5496921453440577942826913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14658457209174874514205101 5496921453440577942826913)
            ·
              refine ⟨4122691090080433457120185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496921453440577942826913 4122691090080433457120185)
              ·
                refine ⟨3092018317560325092840139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122691090080433457120185 3092018317560325092840139)
                ·
                  refine ⟨4638027476340487639260209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092018317560325092840139 4638027476340487639260209)
                  ·
                    refine ⟨3478520607255365729445157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638027476340487639260209 3478520607255365729445157)
                    ·
                      refine ⟨652222613860381074270967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3478520607255365729445157 652222613860381074270967)
                      ·
                        rfl

theorem cell23_1270199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_1270199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270199 prefixEnd_1270199 := by exact prefixLift 1270199
  have htrace : WordTrace (prefixWord ++ tailWord_1270199) baseStart_1270199 baseEnd_1270199 := by
    simpa [prefixWord, tailWord_1270199, baseEnd_1270199] using wordTrace_append hprefix tailTrace_1270199
  have hstable : (prefixWord ++ tailWord_1270199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270199).length < 2 ^ (prefixWord ++ tailWord_1270199).sum := by decide
  have hdescent : baseEnd_1270199 < baseStart_1270199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270220 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1270220 : Nat := 118140960795 + 1270220 * 2 ^ 59
def prefixEnd_1270220 : Nat := 4983230072969 + 3 ^ 40 * 1270220 * 2
def baseEnd_1270220 : Nat := 652233396954125492108371

theorem tailTrace_1270220 : CollatzResearch.WordTrace tailWord_1270220 prefixEnd_1270220 652233396954125492108371 := by
  unfold tailWord_1270220
  simp only [CollatzResearch.WordTrace]
  refine ⟨23164364729108675574964057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30885819638811567433285409 23164364729108675574964057)
  ·
    refine ⟨17373273546831506681223043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23164364729108675574964057 17373273546831506681223043)
    ·
      refine ⟨26059910320247260021834565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17373273546831506681223043 26059910320247260021834565)
      ·
        refine ⟨4886233185046361254093981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26059910320247260021834565 4886233185046361254093981)
        ·
          refine ⟨1832337444392385470285243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4886233185046361254093981 1832337444392385470285243)
          ·
            refine ⟨2748506166588578205427865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832337444392385470285243 2748506166588578205427865)
            ·
              refine ⟨2061379624941433654070899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748506166588578205427865 2061379624941433654070899)
              ·
                refine ⟨3092069437412150481106349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061379624941433654070899 3092069437412150481106349)
                ·
                  refine ⟨1159526039029556430414881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3092069437412150481106349 1159526039029556430414881)
                  ·
                    refine ⟨869644529272167322811161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1159526039029556430414881 869644529272167322811161)
                    ·
                      refine ⟨652233396954125492108371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869644529272167322811161 652233396954125492108371)
                      ·
                        rfl

theorem cell23_1270220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1270220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270220 prefixEnd_1270220 := by exact prefixLift 1270220
  have htrace : WordTrace (prefixWord ++ tailWord_1270220) baseStart_1270220 baseEnd_1270220 := by
    simpa [prefixWord, tailWord_1270220, baseEnd_1270220] using wordTrace_append hprefix tailTrace_1270220
  have hstable : (prefixWord ++ tailWord_1270220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270220).length < 2 ^ (prefixWord ++ tailWord_1270220).sum := by decide
  have hdescent : baseEnd_1270220 < baseStart_1270220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270230 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1270230 : Nat := 118140960795 + 1270230 * 2 ^ 59
def prefixEnd_1270230 : Nat := 4983230072969 + 3 ^ 40 * 1270230 * 2
def baseEnd_1270230 : Nat := 217412843920223484327775

theorem tailTrace_1270230 : CollatzResearch.WordTrace tailWord_1270230 prefixEnd_1270230 217412843920223484327775 := by
  unfold tailWord_1270230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895568386761320178612009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30886062792120748571861429 2895568386761320178612009)
  ·
    refine ⟨2171676290070990133959007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2895568386761320178612009 2171676290070990133959007)
    ·
      refine ⟨3257514435106485200938511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171676290070990133959007 3257514435106485200938511)
      ·
        refine ⟨4886271652659727801407767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257514435106485200938511 4886271652659727801407767)
        ·
          refine ⟨7329407478989591702111651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886271652659727801407767 7329407478989591702111651)
          ·
            refine ⟨10994111218484387553167477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329407478989591702111651 10994111218484387553167477)
            ·
              refine ⟨1030697926732911333109451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10994111218484387553167477 1030697926732911333109451)
              ·
                refine ⟨1546046890099366999664177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030697926732911333109451 1546046890099366999664177)
                ·
                  refine ⟨1159535167574525249748133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546046890099366999664177 1159535167574525249748133)
                  ·
                    refine ⟨217412843920223484327775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159535167574525249748133 217412843920223484327775)
                    ·
                      rfl

theorem cell23_1270230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1270230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270230 prefixEnd_1270230 := by exact prefixLift 1270230
  have htrace : WordTrace (prefixWord ++ tailWord_1270230) baseStart_1270230 baseEnd_1270230 := by
    simpa [prefixWord, tailWord_1270230, baseEnd_1270230] using wordTrace_append hprefix tailTrace_1270230
  have hstable : (prefixWord ++ tailWord_1270230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270230).length < 2 ^ (prefixWord ++ tailWord_1270230).sum := by decide
  have hdescent : baseEnd_1270230 < baseStart_1270230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270243 : List Nat := [1, 1, 1, 6, 4, 1, 2, 7]
def baseStart_1270243 : Nat := 118140960795 + 1270243 * 2 ^ 59
def prefixEnd_1270243 : Nat := 4983230072969 + 3 ^ 40 * 1270243 * 2
def baseEnd_1270243 : Nat := 24157229889228848226695

theorem tailTrace_1270243 : CollatzResearch.WordTrace tailWord_1270243 prefixEnd_1270243 24157229889228848226695 := by
  unfold tailWord_1270243
  simp only [CollatzResearch.WordTrace]
  refine ⟨46329568337134026078015383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30886378891422684052010255 46329568337134026078015383)
  ·
    refine ⟨69494352505701039117023075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46329568337134026078015383 69494352505701039117023075)
    ·
      refine ⟨104241528758551558675534613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69494352505701039117023075 104241528758551558675534613)
      ·
        refine ⟨4886321660557104312915685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104241528758551558675534613 4886321660557104312915685)
        ·
          refine ⟨916185311354457058671691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4886321660557104312915685 916185311354457058671691)
          ·
            refine ⟨1374277967031685588007537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916185311354457058671691 1374277967031685588007537)
            ·
              refine ⟨1030708475273764191005653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1374277967031685588007537 1030708475273764191005653)
              ·
                refine ⟨24157229889228848226695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1030708475273764191005653 24157229889228848226695)
                ·
                  rfl

theorem cell23_1270243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 7].length) (baseStart_1270243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270243 prefixEnd_1270243 := by exact prefixLift 1270243
  have htrace : WordTrace (prefixWord ++ tailWord_1270243) baseStart_1270243 baseEnd_1270243 := by
    simpa [prefixWord, tailWord_1270243, baseEnd_1270243] using wordTrace_append hprefix tailTrace_1270243
  have hstable : (prefixWord ++ tailWord_1270243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270243).length < 2 ^ (prefixWord ++ tailWord_1270243).sum := by decide
  have hdescent : baseEnd_1270243 < baseStart_1270243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270253 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1270253 : Nat := 118140960795 + 1270253 * 2 ^ 59
def prefixEnd_1270253 : Nat := 4983230072969 + 3 ^ 40 * 1270253 * 2
def baseEnd_1270253 : Nat := 652250341815723862995719

theorem tailTrace_1270253 : CollatzResearch.WordTrace tailWord_1270253 prefixEnd_1270253 652250341815723862995719 := by
  unfold tailWord_1270253
  simp only [CollatzResearch.WordTrace]
  refine ⟨46329933067097797785879413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30886622044731865190586275 46329933067097797785879413)
  ·
    refine ⟨4343431225040418542426195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46329933067097797785879413 4343431225040418542426195)
    ·
      refine ⟨6515146837560627813639293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4343431225040418542426195 6515146837560627813639293)
      ·
        refine ⟨2443180064085235430114735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6515146837560627813639293 2443180064085235430114735)
        ·
          refine ⟨3664770096127853145172103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443180064085235430114735 3664770096127853145172103)
          ·
            refine ⟨5497155144191779717758155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664770096127853145172103 5497155144191779717758155)
            ·
              refine ⟨8245732716287669576637233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497155144191779717758155 8245732716287669576637233)
              ·
                refine ⟨6184299537215752182477925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8245732716287669576637233 6184299537215752182477925)
                ·
                  refine ⟨1159556163227953534214611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6184299537215752182477925 1159556163227953534214611)
                  ·
                    refine ⟨1739334244841930301321917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1159556163227953534214611 1739334244841930301321917)
                    ·
                      refine ⟨652250341815723862995719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1739334244841930301321917 652250341815723862995719)
                      ·
                        rfl

theorem cell23_1270253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1270253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270253 prefixEnd_1270253 := by exact prefixLift 1270253
  have htrace : WordTrace (prefixWord ++ tailWord_1270253) baseStart_1270253 baseEnd_1270253 := by
    simpa [prefixWord, tailWord_1270253, baseEnd_1270253] using wordTrace_append hprefix tailTrace_1270253
  have hstable : (prefixWord ++ tailWord_1270253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270253).length < 2 ^ (prefixWord ++ tailWord_1270253).sum := by decide
  have hdescent : baseEnd_1270253 < baseStart_1270253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270333 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 5]
def baseStart_1270333 : Nat := 118140960795 + 1270333 * 2 ^ 59
def prefixEnd_1270333 : Nat := 4983230072969 + 3 ^ 40 * 1270333 * 2
def baseEnd_1270333 : Nat := 72476824474231505555039

theorem tailTrace_1270333 : CollatzResearch.WordTrace tailWord_1270333 prefixEnd_1270333 72476824474231505555039 := by
  unfold tailWord_1270333
  simp only [CollatzResearch.WordTrace]
  refine ⟨46332850906807971448791653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30888567271205314299194435 46332850906807971448791653)
  ·
    refine ⟨8687409545026494646648435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46332850906807971448791653 8687409545026494646648435)
    ·
      refine ⟨13031114317539741969972653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8687409545026494646648435 13031114317539741969972653)
      ·
        refine ⟨4886667869077403238739745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13031114317539741969972653 4886667869077403238739745)
        ·
          refine ⟨3665000901808052429054809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4886667869077403238739745 3665000901808052429054809)
          ·
            refine ⟨2748750676356039321791107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3665000901808052429054809 2748750676356039321791107)
            ·
              refine ⟨4123126014534058982686661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748750676356039321791107 4123126014534058982686661)
              ·
                refine ⟨773086127725136059253749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4123126014534058982686661 773086127725136059253749)
                ·
                  refine ⟨72476824474231505555039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 773086127725136059253749 72476824474231505555039)
                  ·
                    rfl

theorem cell23_1270333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_1270333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270333 prefixEnd_1270333 := by exact prefixLift 1270333
  have htrace : WordTrace (prefixWord ++ tailWord_1270333) baseStart_1270333 baseEnd_1270333 := by
    simpa [prefixWord, tailWord_1270333, baseEnd_1270333] using wordTrace_append hprefix tailTrace_1270333
  have hstable : (prefixWord ++ tailWord_1270333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270333).length < 2 ^ (prefixWord ++ tailWord_1270333).sum := by decide
  have hdescent : baseEnd_1270333 < baseStart_1270333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270336 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 2, 5, 2]
def baseStart_1270336 : Nat := 118140960795 + 1270336 * 2 ^ 59
def prefixEnd_1270336 : Nat := 4983230072969 + 3 ^ 40 * 1270336 * 2
def baseEnd_1270336 : Nat := 652292960710047038257837

theorem tailTrace_1270336 : CollatzResearch.WordTrace tailWord_1270336 prefixEnd_1270336 652292960710047038257837 := by
  unfold tailWord_1270336
  simp only [CollatzResearch.WordTrace]
  refine ⟨23166480162898551480575431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30888640217198068640767241 23166480162898551480575431)
  ·
    refine ⟨34749720244347827220863147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23166480162898551480575431 34749720244347827220863147)
    ·
      refine ⟨52124580366521740831294721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34749720244347827220863147 52124580366521740831294721)
      ·
        refine ⟨39093435274891305623471041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52124580366521740831294721 39093435274891305623471041)
        ·
          refine ⟨29320076456168479217603281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39093435274891305623471041 29320076456168479217603281)
          ·
            refine ⟨21990057342126359413202461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29320076456168479217603281 21990057342126359413202461)
            ·
              refine ⟨8246271503297384779950923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21990057342126359413202461 8246271503297384779950923)
              ·
                refine ⟨12369407254946077169926385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8246271503297384779950923 12369407254946077169926385)
                ·
                  refine ⟨9277055441209557877444789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12369407254946077169926385 9277055441209557877444789)
                  ·
                    refine ⟨869723947613396051010449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9277055441209557877444789 869723947613396051010449)
                    ·
                      refine ⟨652292960710047038257837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869723947613396051010449 652292960710047038257837)
                      ·
                        rfl

theorem cell23_1270336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_1270336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270336 prefixEnd_1270336 := by exact prefixLift 1270336
  have htrace : WordTrace (prefixWord ++ tailWord_1270336) baseStart_1270336 baseEnd_1270336 := by
    simpa [prefixWord, tailWord_1270336, baseEnd_1270336] using wordTrace_append hprefix tailTrace_1270336
  have hstable : (prefixWord ++ tailWord_1270336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270336).length < 2 ^ (prefixWord ++ tailWord_1270336).sum := by decide
  have hdescent : baseEnd_1270336 < baseStart_1270336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270393 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 3, 4]
def baseStart_1270393 : Nat := 118140960795 + 1270393 * 2 ^ 59
def prefixEnd_1270393 : Nat := 4983230072969 + 3 ^ 40 * 1270393 * 2
def baseEnd_1270393 : Nat := 217440743035784438415025

theorem tailTrace_1270393 : CollatzResearch.WordTrace tailWord_1270393 prefixEnd_1270393 217440743035784438415025 := by
  unfold tailWord_1270393
  simp only [CollatzResearch.WordTrace]
  refine ⟨46335039286590601695975833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30890026191060401130650555 46335039286590601695975833)
  ·
    refine ⟨34751279464942951271981875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46335039286590601695975833 34751279464942951271981875)
    ·
      refine ⟨52126919197414426907972813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34751279464942951271981875 52126919197414426907972813)
      ·
        refine ⟨19547594699030410090489805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52126919197414426907972813 19547594699030410090489805)
        ·
          refine ⟨7330348012136403783933677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19547594699030410090489805 7330348012136403783933677)
          ·
            refine ⟨2748880504551151418975129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7330348012136403783933677 2748880504551151418975129)
            ·
              refine ⟨2061660378413363564231347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748880504551151418975129 2061660378413363564231347)
              ·
                refine ⟨3092490567620045346347021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061660378413363564231347 3092490567620045346347021)
                ·
                  refine ⟨1159683962857517004880133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3092490567620045346347021 1159683962857517004880133)
                  ·
                    refine ⟨217440743035784438415025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159683962857517004880133 217440743035784438415025)
                    ·
                      rfl

theorem cell23_1270393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_1270393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270393 prefixEnd_1270393 := by exact prefixLift 1270393
  have htrace : WordTrace (prefixWord ++ tailWord_1270393) baseStart_1270393 baseEnd_1270393 := by
    simpa [prefixWord, tailWord_1270393, baseEnd_1270393] using wordTrace_append hprefix tailTrace_1270393
  have hstable : (prefixWord ++ tailWord_1270393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270393).length < 2 ^ (prefixWord ++ tailWord_1270393).sum := by decide
  have hdescent : baseEnd_1270393 < baseStart_1270393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270409 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_1270409 : Nat := 118140960795 + 1270409 * 2 ^ 59
def prefixEnd_1270409 : Nat := 4983230072969 + 3 ^ 40 * 1270409 * 2
def baseEnd_1270409 : Nat := 652330444797825252645001

theorem tailTrace_1270409 : CollatzResearch.WordTrace tailWord_1270409 prefixEnd_1270409 652330444797825252645001 := by
  unfold tailWord_1270409
  simp only [CollatzResearch.WordTrace]
  refine ⟨46335622854532636428558281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30890415236355090952372187 46335622854532636428558281)
  ·
    refine ⟨34751717140899477321418711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46335622854532636428558281 34751717140899477321418711)
    ·
      refine ⟨52127575711349215982128067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34751717140899477321418711 52127575711349215982128067)
      ·
        refine ⟨78191363567023823973192101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52127575711349215982128067 78191363567023823973192101)
        ·
          refine ⟨14660880668816966994973519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78191363567023823973192101 14660880668816966994973519)
          ·
            refine ⟨21991321003225450492460279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14660880668816966994973519 21991321003225450492460279)
            ·
              refine ⟨32986981504838175738690419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21991321003225450492460279 32986981504838175738690419)
              ·
                refine ⟨49480472257257263608035629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32986981504838175738690419 49480472257257263608035629)
                ·
                  refine ⟨18555177096471473853013361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49480472257257263608035629 18555177096471473853013361)
                  ·
                    refine ⟨13916382822353605389760021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18555177096471473853013361 13916382822353605389760021)
                    ·
                      refine ⟨652330444797825252645001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13916382822353605389760021 652330444797825252645001)
                      ·
                        rfl

theorem cell23_1270409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_1270409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270409 prefixEnd_1270409 := by exact prefixLift 1270409
  have htrace : WordTrace (prefixWord ++ tailWord_1270409) baseStart_1270409 baseEnd_1270409 := by
    simpa [prefixWord, tailWord_1270409, baseEnd_1270409] using wordTrace_append hprefix tailTrace_1270409
  have hstable : (prefixWord ++ tailWord_1270409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270409).length < 2 ^ (prefixWord ++ tailWord_1270409).sum := by decide
  have hdescent : baseEnd_1270409 < baseStart_1270409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270490 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4]
def baseStart_1270490 : Nat := 118140960795 + 1270490 * 2 ^ 59
def prefixEnd_1270490 : Nat := 4983230072969 + 3 ^ 40 * 1270490 * 2
def baseEnd_1270490 : Nat := 652372036730839435732129

theorem tailTrace_1270490 : CollatzResearch.WordTrace tailWord_1270490 prefixEnd_1270490 652372036730839435732129 := by
  unfold tailWord_1270490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584644291809796815564231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30892384778159458174837949 11584644291809796815564231)
  ·
    refine ⟨17376966437714695223346347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11584644291809796815564231 17376966437714695223346347)
    ·
      refine ⟨26065449656572042835019521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17376966437714695223346347 26065449656572042835019521)
      ·
        refine ⟨19549087242429032126264641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26065449656572042835019521 19549087242429032126264641)
        ·
          refine ⟨14661815431821774094698481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19549087242429032126264641 14661815431821774094698481)
          ·
            refine ⟨10996361573866330571023861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14661815431821774094698481 10996361573866330571023861)
            ·
              refine ⟨1030908897549968491033487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10996361573866330571023861 1030908897549968491033487)
              ·
                refine ⟨1546363346324952736550231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030908897549968491033487 1546363346324952736550231)
                ·
                  refine ⟨2319545019487429104825347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546363346324952736550231 2319545019487429104825347)
                  ·
                    refine ⟨3479317529231143657238021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2319545019487429104825347 3479317529231143657238021)
                    ·
                      refine ⟨652372036730839435732129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3479317529231143657238021 652372036730839435732129)
                      ·
                        rfl

theorem cell23_1270490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_1270490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270490 prefixEnd_1270490 := by exact prefixLift 1270490
  have htrace : WordTrace (prefixWord ++ tailWord_1270490) baseStart_1270490 baseEnd_1270490 := by
    simpa [prefixWord, tailWord_1270490, baseEnd_1270490] using wordTrace_append hprefix tailTrace_1270490
  have hstable : (prefixWord ++ tailWord_1270490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270490).length < 2 ^ (prefixWord ++ tailWord_1270490).sum := by decide
  have hdescent : baseEnd_1270490 < baseStart_1270490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270500 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_1270500 : Nat := 118140960795 + 1270500 * 2 ^ 59
def prefixEnd_1270500 : Nat := 4983230072969 + 3 ^ 40 * 1270500 * 2
def baseEnd_1270500 : Nat := 217459057179128132202361

theorem tailTrace_1270500 : CollatzResearch.WordTrace tailWord_1270500 prefixEnd_1270500 217459057179128132202361 := by
  unfold tailWord_1270500
  simp only [CollatzResearch.WordTrace]
  refine ⟨23169470948601479485060477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30892627931468639313413969 23169470948601479485060477)
  ·
    refine ⟨8688551605725554806897679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23169470948601479485060477 8688551605725554806897679)
    ·
      refine ⟨13032827408588332210346519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688551605725554806897679 13032827408588332210346519)
      ·
        refine ⟨19549241112882498315519779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13032827408588332210346519 19549241112882498315519779)
        ·
          refine ⟨29323861669323747473279669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19549241112882498315519779 29323861669323747473279669)
          ·
            refine ⟨2749112031499101325619969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29323861669323747473279669 2749112031499101325619969)
            ·
              refine ⟨2061834023624325994214977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749112031499101325619969 2061834023624325994214977)
              ·
                refine ⟨1546375517718244495661233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061834023624325994214977 1546375517718244495661233)
                ·
                  refine ⟨1159781638288683371745925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546375517718244495661233 1159781638288683371745925)
                  ·
                    refine ⟨217459057179128132202361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1159781638288683371745925 217459057179128132202361)
                    ·
                      rfl

theorem cell23_1270500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_1270500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270500 prefixEnd_1270500 := by exact prefixLift 1270500
  have htrace : WordTrace (prefixWord ++ tailWord_1270500) baseStart_1270500 baseEnd_1270500 := by
    simpa [prefixWord, tailWord_1270500, baseEnd_1270500] using wordTrace_append hprefix tailTrace_1270500
  have hstable : (prefixWord ++ tailWord_1270500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270500).length < 2 ^ (prefixWord ++ tailWord_1270500).sum := by decide
  have hdescent : baseEnd_1270500 < baseStart_1270500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270530 : List Nat := [3, 4, 1, 1, 1, 3, 3, 7]
def baseStart_1270530 : Nat := 118140960795 + 1270530 * 2 ^ 59
def prefixEnd_1270530 : Nat := 4983230072969 + 3 ^ 40 * 1270530 * 2
def baseEnd_1270530 : Nat := 24162687998408121453035

theorem tailTrace_1270530 : CollatzResearch.WordTrace tailWord_1270530 prefixEnd_1270530 24162687998408121453035 := by
  unfold tailWord_1270530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585009021773568523428261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30893357391396182729142029 11585009021773568523428261)
  ·
    refine ⟨2172189191582544098142799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11585009021773568523428261 2172189191582544098142799)
    ·
      refine ⟨3258283787373816147214199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172189191582544098142799 3258283787373816147214199)
      ·
        refine ⟨4887425681060724220821299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258283787373816147214199 4887425681060724220821299)
        ·
          refine ⟨7331138521591086331231949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887425681060724220821299 7331138521591086331231949)
          ·
            refine ⟨2749176945596657374211981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7331138521591086331231949 2749176945596657374211981)
            ·
              refine ⟨1030941354598746515329493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2749176945596657374211981 1030941354598746515329493)
              ·
                refine ⟨24162687998408121453035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1030941354598746515329493 24162687998408121453035)
                ·
                  rfl

theorem cell23_1270530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_1270530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270530 prefixEnd_1270530 := by exact prefixLift 1270530
  have htrace : WordTrace (prefixWord ++ tailWord_1270530) baseStart_1270530 baseEnd_1270530 := by
    simpa [prefixWord, tailWord_1270530, baseEnd_1270530] using wordTrace_append hprefix tailTrace_1270530
  have hstable : (prefixWord ++ tailWord_1270530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270530).length < 2 ^ (prefixWord ++ tailWord_1270530).sum := by decide
  have hdescent : baseEnd_1270530 < baseStart_1270530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270620 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 7]
def baseStart_1270620 : Nat := 118140960795 + 1270620 * 2 ^ 59
def prefixEnd_1270620 : Nat := 4983230072969 + 3 ^ 40 * 1270620 * 2
def baseEnd_1270620 : Nat := 72493198801769325234059

theorem tailTrace_1270620 : CollatzResearch.WordTrace tailWord_1270620 prefixEnd_1270620 72493198801769325234059 := by
  unfold tailWord_1270620
  simp only [CollatzResearch.WordTrace]
  refine ⟨23171659328384109732244657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30895545771178812976326209 23171659328384109732244657)
  ·
    refine ⟨17378744496288082299183493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23171659328384109732244657 17378744496288082299183493)
    ·
      refine ⟨3258514593054015431096905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17378744496288082299183493 3258514593054015431096905)
      ·
        refine ⟨2443885944790511573322679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3258514593054015431096905 2443885944790511573322679)
        ·
          refine ⟨3665828917185767359984019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443885944790511573322679 3665828917185767359984019)
          ·
            refine ⟨5498743375778651039976029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665828917185767359984019 5498743375778651039976029)
            ·
              refine ⟨2062028765916994139991011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5498743375778651039976029 2062028765916994139991011)
              ·
                refine ⟨3093043148875491209986517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062028765916994139991011 3093043148875491209986517)
                ·
                  refine ⟨72493198801769325234059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3093043148875491209986517 72493198801769325234059)
                  ·
                    rfl

theorem cell23_1270620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_1270620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270620 prefixEnd_1270620 := by exact prefixLift 1270620
  have htrace : WordTrace (prefixWord ++ tailWord_1270620) baseStart_1270620 baseEnd_1270620 := by
    simpa [prefixWord, tailWord_1270620, baseEnd_1270620] using wordTrace_append hprefix tailTrace_1270620
  have hstable : (prefixWord ++ tailWord_1270620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270620).length < 2 ^ (prefixWord ++ tailWord_1270620).sum := by decide
  have hdescent : baseEnd_1270620 < baseStart_1270620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270631 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 2, 2, 2]
def baseStart_1270631 : Nat := 118140960795 + 1270631 * 2 ^ 59
def prefixEnd_1270631 : Nat := 4983230072969 + 3 ^ 40 * 1270631 * 2
def baseEnd_1270631 : Nat := 652444437503123384068981

theorem tailTrace_1270631 : CollatzResearch.WordTrace tailWord_1270631 prefixEnd_1270631 652444437503123384068981 := by
  unfold tailWord_1270631
  simp only [CollatzResearch.WordTrace]
  refine ⟨46343719859728368343139747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30895813239818912228759831 46343719859728368343139747)
  ·
    refine ⟨69515579789592552514709621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46343719859728368343139747 69515579789592552514709621)
    ·
      refine ⟨6517085605274301798254027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69515579789592552514709621 6517085605274301798254027)
      ·
        refine ⟨9775628407911452697381041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517085605274301798254027 9775628407911452697381041)
        ·
          refine ⟨7331721305933589523035781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9775628407911452697381041 7331721305933589523035781)
          ·
            refine ⟨1374697744862548035569209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7331721305933589523035781 1374697744862548035569209)
            ·
              refine ⟨1031023308646911026676907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1374697744862548035569209 1031023308646911026676907)
              ·
                refine ⟨1546534962970366540015361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031023308646911026676907 1546534962970366540015361)
                ·
                  refine ⟨1159901222227774905011521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546534962970366540015361 1159901222227774905011521)
                  ·
                    refine ⟨869925916670831178758641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1159901222227774905011521 869925916670831178758641)
                    ·
                      refine ⟨652444437503123384068981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869925916670831178758641 652444437503123384068981)
                      ·
                        rfl

theorem cell23_1270631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_1270631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270631 prefixEnd_1270631 := by exact prefixLift 1270631
  have htrace : WordTrace (prefixWord ++ tailWord_1270631) baseStart_1270631 baseEnd_1270631 := by
    simpa [prefixWord, tailWord_1270631, baseEnd_1270631] using wordTrace_append hprefix tailTrace_1270631
  have hstable : (prefixWord ++ tailWord_1270631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270631).length < 2 ^ (prefixWord ++ tailWord_1270631).sum := by decide
  have hdescent : baseEnd_1270631 < baseStart_1270631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270653 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1270653 : Nat := 118140960795 + 1270653 * 2 ^ 59
def prefixEnd_1270653 : Nat := 4983230072969 + 3 ^ 40 * 1270653 * 2
def baseEnd_1270653 : Nat := 652455734077522297993879

theorem tailTrace_1270653 : CollatzResearch.WordTrace tailWord_1270653 prefixEnd_1270653 652455734077522297993879 := by
  unfold tailWord_1270653
  simp only [CollatzResearch.WordTrace]
  refine ⟨46344522265648666100440613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30896348177099110733627075 46344522265648666100440613)
  ·
    refine ⟨8689597924809124893832615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46344522265648666100440613 8689597924809124893832615)
    ·
      refine ⟨13034396887213687340748923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8689597924809124893832615 13034396887213687340748923)
      ·
        refine ⟨19551595330820531011123385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13034396887213687340748923 19551595330820531011123385)
        ·
          refine ⟨14663696498115398258342539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19551595330820531011123385 14663696498115398258342539)
          ·
            refine ⟨21995544747173097387513809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14663696498115398258342539 21995544747173097387513809)
            ·
              refine ⟨16496658560379823040635357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21995544747173097387513809 16496658560379823040635357)
              ·
                refine ⟨6186246960142433640238259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16496658560379823040635357 6186246960142433640238259)
                ·
                  refine ⟨9279370440213650460357389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6186246960142433640238259 9279370440213650460357389)
                  ·
                    refine ⟨3479763915080118922634021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9279370440213650460357389 3479763915080118922634021)
                    ·
                      refine ⟨652455734077522297993879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3479763915080118922634021 652455734077522297993879)
                      ·
                        rfl

theorem cell23_1270653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1270653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270653 prefixEnd_1270653 := by exact prefixLift 1270653
  have htrace : WordTrace (prefixWord ++ tailWord_1270653) baseStart_1270653 baseEnd_1270653 := by
    simpa [prefixWord, tailWord_1270653, baseEnd_1270653] using wordTrace_append hprefix tailTrace_1270653
  have hstable : (prefixWord ++ tailWord_1270653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270653).length < 2 ^ (prefixWord ++ tailWord_1270653).sum := by decide
  have hdescent : baseEnd_1270653 < baseStart_1270653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270673 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_1270673 : Nat := 118140960795 + 1270673 * 2 ^ 59
def prefixEnd_1270673 : Nat := 4983230072969 + 3 ^ 40 * 1270673 * 2
def baseEnd_1270673 : Nat := 652466003690612219743787

theorem tailTrace_1270673 : CollatzResearch.WordTrace tailWord_1270673 prefixEnd_1270673 652466003690612219743787 := by
  unfold tailWord_1270673
  simp only [CollatzResearch.WordTrace]
  refine ⟨46345251725576209516168673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30896834483717473010779115 46345251725576209516168673)
  ·
    refine ⟨34758938794182157137126505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46345251725576209516168673 34758938794182157137126505)
    ·
      refine ⟨26069204095636617852844879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34758938794182157137126505 26069204095636617852844879)
      ·
        refine ⟨39103806143454926779267319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26069204095636617852844879 39103806143454926779267319)
        ·
          refine ⟨58655709215182390168900979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39103806143454926779267319 58655709215182390168900979)
          ·
            refine ⟨87983563822773585253351469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58655709215182390168900979 87983563822773585253351469)
            ·
              refine ⟨32993836433540094470006801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87983563822773585253351469 32993836433540094470006801)
              ·
                refine ⟨24745377325155070852505101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32993836433540094470006801 24745377325155070852505101)
                ·
                  refine ⟨9279516496933151569689413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24745377325155070852505101 9279516496933151569689413)
                  ·
                    refine ⟨1739909343174965919316765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9279516496933151569689413 1739909343174965919316765)
                    ·
                      refine ⟨652466003690612219743787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1739909343174965919316765 652466003690612219743787)
                      ·
                        rfl

theorem cell23_1270673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_1270673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270673 prefixEnd_1270673 := by exact prefixLift 1270673
  have htrace : WordTrace (prefixWord ++ tailWord_1270673) baseStart_1270673 baseEnd_1270673 := by
    simpa [prefixWord, tailWord_1270673, baseEnd_1270673] using wordTrace_append hprefix tailTrace_1270673
  have hstable : (prefixWord ++ tailWord_1270673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270673).length < 2 ^ (prefixWord ++ tailWord_1270673).sum := by decide
  have hdescent : baseEnd_1270673 < baseStart_1270673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270687 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1270687 : Nat := 118140960795 + 1270687 * 2 ^ 59
def prefixEnd_1270687 : Nat := 4983230072969 + 3 ^ 40 * 1270687 * 2
def baseEnd_1270687 : Nat := 652473192419775164968723

theorem tailTrace_1270687 : CollatzResearch.WordTrace tailWord_1270687 prefixEnd_1270687 652473192419775164968723 := by
  unfold tailWord_1270687
  simp only [CollatzResearch.WordTrace]
  refine ⟨46345762347525489907178315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30897174898350326604785543 46345762347525489907178315)
  ·
    refine ⟨69518643521288234860767473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46345762347525489907178315 69518643521288234860767473)
    ·
      refine ⟨52138982640966176145575605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69518643521288234860767473 52138982640966176145575605)
      ·
        refine ⟨4888029622590579013647713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52138982640966176145575605 4888029622590579013647713)
        ·
          refine ⟨3666022216942934260235785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4888029622590579013647713 3666022216942934260235785)
          ·
            refine ⟨2749516662707200695176839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3666022216942934260235785 2749516662707200695176839)
            ·
              refine ⟨4124274994060801042765259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749516662707200695176839 4124274994060801042765259)
              ·
                refine ⟨6186412491091201564147889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124274994060801042765259 6186412491091201564147889)
                ·
                  refine ⟨4639809368318401173110917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6186412491091201564147889 4639809368318401173110917)
                  ·
                    refine ⟨869964256559700219958297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4639809368318401173110917 869964256559700219958297)
                    ·
                      refine ⟨652473192419775164968723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 869964256559700219958297 652473192419775164968723)
                      ·
                        rfl

theorem cell23_1270687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1270687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270687 prefixEnd_1270687 := by exact prefixLift 1270687
  have htrace : WordTrace (prefixWord ++ tailWord_1270687) baseStart_1270687 baseEnd_1270687 := by
    simpa [prefixWord, tailWord_1270687, baseEnd_1270687] using wordTrace_append hprefix tailTrace_1270687
  have hstable : (prefixWord ++ tailWord_1270687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270687).length < 2 ^ (prefixWord ++ tailWord_1270687).sum := by decide
  have hdescent : baseEnd_1270687 < baseStart_1270687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270701 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1270701 : Nat := 118140960795 + 1270701 * 2 ^ 59
def prefixEnd_1270701 : Nat := 4983230072969 + 3 ^ 40 * 1270701 * 2
def baseEnd_1270701 : Nat := 217493460382979370064553

theorem tailTrace_1270701 : CollatzResearch.WordTrace tailWord_1270701 prefixEnd_1270701 217493460382979370064553 := by
  unfold tailWord_1270701
  simp only [CollatzResearch.WordTrace]
  refine ⟨46346272969474770298187957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30897515312983180198791971 46346272969474770298187957)
  ·
    refine ⟨4344963090888259715455121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46346272969474770298187957 4344963090888259715455121)
    ·
      refine ⟨3258722318166194786591341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4344963090888259715455121 3258722318166194786591341)
      ·
        refine ⟨1222020869312323044971753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3258722318166194786591341 1222020869312323044971753)
        ·
          refine ⟨916515651984242283728815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222020869312323044971753 916515651984242283728815)
          ·
            refine ⟨1374773477976363425593223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916515651984242283728815 1374773477976363425593223)
            ·
              refine ⟨2062160216964545138389835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374773477976363425593223 2062160216964545138389835)
              ·
                refine ⟨3093240325446817707584753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062160216964545138389835 3093240325446817707584753)
                ·
                  refine ⟨2319930244085113280688565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3093240325446817707584753 2319930244085113280688565)
                  ·
                    refine ⟨217493460382979370064553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2319930244085113280688565 217493460382979370064553)
                    ·
                      rfl

theorem cell23_1270701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1270701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270701 prefixEnd_1270701 := by exact prefixLift 1270701
  have htrace : WordTrace (prefixWord ++ tailWord_1270701) baseStart_1270701 baseEnd_1270701 := by
    simpa [prefixWord, tailWord_1270701, baseEnd_1270701] using wordTrace_append hprefix tailTrace_1270701
  have hstable : (prefixWord ++ tailWord_1270701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270701).length < 2 ^ (prefixWord ++ tailWord_1270701).sum := by decide
  have hdescent : baseEnd_1270701 < baseStart_1270701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270703 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 3]
def baseStart_1270703 : Nat := 118140960795 + 1270703 * 2 ^ 59
def prefixEnd_1270703 : Nat := 4983230072969 + 3 ^ 40 * 1270703 * 2
def baseEnd_1270703 : Nat := 652481408110247102368649

theorem tailTrace_1270703 : CollatzResearch.WordTrace tailWord_1270703 prefixEnd_1270703 652481408110247102368649 := by
  unfold tailWord_1270703
  simp only [CollatzResearch.WordTrace]
  refine ⟨46346345915467524639760763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30897563943645016426507175 46346345915467524639760763)
  ·
    refine ⟨69519518873201286959641145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46346345915467524639760763 69519518873201286959641145)
    ·
      refine ⟨52139639154900965219730859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69519518873201286959641145 52139639154900965219730859)
      ·
        refine ⟨78209458732351447829596289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52139639154900965219730859 78209458732351447829596289)
        ·
          refine ⟨58657094049263585872197217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78209458732351447829596289 58657094049263585872197217)
          ·
            refine ⟨43992820536947689404147913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58657094049263585872197217 43992820536947689404147913)
            ·
              refine ⟨32994615402710767053110935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43992820536947689404147913 32994615402710767053110935)
              ·
                refine ⟨49491923104066150579666403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32994615402710767053110935 49491923104066150579666403)
                ·
                  refine ⟨74237884656099225869499605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49491923104066150579666403 74237884656099225869499605)
                  ·
                    refine ⟨1739950421627325606316397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 74237884656099225869499605 1739950421627325606316397)
                    ·
                      refine ⟨652481408110247102368649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1739950421627325606316397 652481408110247102368649)
                      ·
                        rfl

theorem cell23_1270703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 3].length) (baseStart_1270703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270703 prefixEnd_1270703 := by exact prefixLift 1270703
  have htrace : WordTrace (prefixWord ++ tailWord_1270703) baseStart_1270703 baseEnd_1270703 := by
    simpa [prefixWord, tailWord_1270703, baseEnd_1270703] using wordTrace_append hprefix tailTrace_1270703
  have hstable : (prefixWord ++ tailWord_1270703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270703).length < 2 ^ (prefixWord ++ tailWord_1270703).sum := by decide
  have hdescent : baseEnd_1270703 < baseStart_1270703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270737 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_1270737 : Nat := 118140960795 + 1270737 * 2 ^ 59
def prefixEnd_1270737 : Nat := 4983230072969 + 3 ^ 40 * 1270737 * 2
def baseEnd_1270737 : Nat := 652498866452499969343493

theorem tailTrace_1270737 : CollatzResearch.WordTrace tailWord_1270737 prefixEnd_1270737 652498866452499969343493 := by
  unfold tailWord_1270737
  simp only [CollatzResearch.WordTrace]
  refine ⟨46347585997344348446498465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30898390664896232297665643 46347585997344348446498465)
  ·
    refine ⟨34760689498008261334873849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46347585997344348446498465 34760689498008261334873849)
    ·
      refine ⟨26070517123506196001155387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34760689498008261334873849 26070517123506196001155387)
      ·
        refine ⟨39105775685259294001733081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26070517123506196001155387 39105775685259294001733081)
        ·
          refine ⟨29329331763944470501299811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39105775685259294001733081 29329331763944470501299811)
          ·
            refine ⟨43993997645916705751949717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29329331763944470501299811 43993997645916705751949717)
            ·
              refine ⟨2062218639652345582122643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43993997645916705751949717 2062218639652345582122643)
              ·
                refine ⟨3093327959478518373183965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062218639652345582122643 3093327959478518373183965)
                ·
                  refine ⟨1159997984804444389943987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3093327959478518373183965 1159997984804444389943987)
                  ·
                    refine ⟨1739996977206666584915981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1159997984804444389943987 1739996977206666584915981)
                    ·
                      refine ⟨652498866452499969343493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1739996977206666584915981 652498866452499969343493)
                      ·
                        rfl

theorem cell23_1270737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_1270737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270737 prefixEnd_1270737 := by exact prefixLift 1270737
  have htrace : WordTrace (prefixWord ++ tailWord_1270737) baseStart_1270737 baseEnd_1270737 := by
    simpa [prefixWord, tailWord_1270737, baseEnd_1270737] using wordTrace_append hprefix tailTrace_1270737
  have hstable : (prefixWord ++ tailWord_1270737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270737).length < 2 ^ (prefixWord ++ tailWord_1270737).sum := by decide
  have hdescent : baseEnd_1270737 < baseStart_1270737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270743 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 4]
def baseStart_1270743 : Nat := 118140960795 + 1270743 * 2 ^ 59
def prefixEnd_1270743 : Nat := 4983230072969 + 3 ^ 40 * 1270743 * 2
def baseEnd_1270743 : Nat := 652501947336426945868465

theorem tailTrace_1270743 : CollatzResearch.WordTrace tailWord_1270743 prefixEnd_1270743 652501947336426945868465 := by
  unfold tailWord_1270743
  simp only [CollatzResearch.WordTrace]
  refine ⟨46347804835322611471216883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30898536556881740980811255 46347804835322611471216883)
  ·
    refine ⟨69521707252983917206825325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46347804835322611471216883 69521707252983917206825325)
    ·
      refine ⟨26070640219868968952559497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69521707252983917206825325 26070640219868968952559497)
      ·
        refine ⟨19552980164901726714419623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26070640219868968952559497 19552980164901726714419623)
        ·
          refine ⟨29329470247352590071629435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19552980164901726714419623 29329470247352590071629435)
          ·
            refine ⟨43994205371028885107444153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29329470247352590071629435 43994205371028885107444153)
            ·
              refine ⟨32995654028271663830583115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43994205371028885107444153 32995654028271663830583115)
              ·
                refine ⟨49493481042407495745874673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32995654028271663830583115 49493481042407495745874673)
                ·
                  refine ⟨37120110781805621809406005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49493481042407495745874673 37120110781805621809406005)
                  ·
                    refine ⟨3480010385794277044631813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37120110781805621809406005 3480010385794277044631813)
                    ·
                      refine ⟨652501947336426945868465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3480010385794277044631813 652501947336426945868465)
                      ·
                        rfl

theorem cell23_1270743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_1270743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270743 prefixEnd_1270743 := by exact prefixLift 1270743
  have htrace : WordTrace (prefixWord ++ tailWord_1270743) baseStart_1270743 baseEnd_1270743 := by
    simpa [prefixWord, tailWord_1270743, baseEnd_1270743] using wordTrace_append hprefix tailTrace_1270743
  have hstable : (prefixWord ++ tailWord_1270743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270743).length < 2 ^ (prefixWord ++ tailWord_1270743).sum := by decide
  have hdescent : baseEnd_1270743 < baseStart_1270743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270760 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1270760 : Nat := 118140960795 + 1270760 * 2 ^ 59
def prefixEnd_1270760 : Nat := 4983230072969 + 3 ^ 40 * 1270760 * 2
def baseEnd_1270760 : Nat := 652510676507553379355887

theorem tailTrace_1270760 : CollatzResearch.WordTrace tailWord_1270760 prefixEnd_1270760 652510676507553379355887 := by
  unfold tailWord_1270760
  simp only [CollatzResearch.WordTrace]
  refine ⟨23174212438130511687292867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30898949917507348916390489 23174212438130511687292867)
  ·
    refine ⟨34761318657195767530939301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23174212438130511687292867 34761318657195767530939301)
    ·
      refine ⟨6517747248224206412051119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34761318657195767530939301 6517747248224206412051119)
      ·
        refine ⟨9776620872336309618076679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517747248224206412051119 9776620872336309618076679)
        ·
          refine ⟨14664931308504464427115019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9776620872336309618076679 14664931308504464427115019)
          ·
            refine ⟨21997396962756696640672529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14664931308504464427115019 21997396962756696640672529)
            ·
              refine ⟨16498047722067522480504397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21997396962756696640672529 16498047722067522480504397)
              ·
                refine ⟨6186767895775320930189149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16498047722067522480504397 6186767895775320930189149)
                ·
                  refine ⟨2320037960915745348820931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6186767895775320930189149 2320037960915745348820931)
                  ·
                    refine ⟨3480056941373618023231397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2320037960915745348820931 3480056941373618023231397)
                    ·
                      refine ⟨652510676507553379355887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3480056941373618023231397 652510676507553379355887)
                      ·
                        rfl

theorem cell23_1270760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1270760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270760 prefixEnd_1270760 := by exact prefixLift 1270760
  have htrace : WordTrace (prefixWord ++ tailWord_1270760) baseStart_1270760 baseEnd_1270760 := by
    simpa [prefixWord, tailWord_1270760, baseEnd_1270760] using wordTrace_append hprefix tailTrace_1270760
  have hstable : (prefixWord ++ tailWord_1270760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270760).length < 2 ^ (prefixWord ++ tailWord_1270760).sum := by decide
  have hdescent : baseEnd_1270760 < baseStart_1270760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270780 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_1270780 : Nat := 118140960795 + 1270780 * 2 ^ 59
def prefixEnd_1270780 : Nat := 4983230072969 + 3 ^ 40 * 1270780 * 2
def baseEnd_1270780 : Nat := 652520946120643301105795

theorem tailTrace_1270780 : CollatzResearch.WordTrace tailWord_1270780 prefixEnd_1270780 652520946120643301105795 := by
  unfold tailWord_1270780
  simp only [CollatzResearch.WordTrace]
  refine ⟨23174577168094283395156897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30899436224125711193542529 23174577168094283395156897)
  ·
    refine ⟨17380932876070712546367673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23174577168094283395156897 17380932876070712546367673)
    ·
      refine ⟨13035699657053034409775755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17380932876070712546367673 13035699657053034409775755)
      ·
        refine ⟨19553549485579551614663633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13035699657053034409775755 19553549485579551614663633)
        ·
          refine ⟨14665162114184663710997725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19553549485579551614663633 14665162114184663710997725)
          ·
            refine ⟨5499435792819248891624147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14665162114184663710997725 5499435792819248891624147)
            ·
              refine ⟨8249153689228873337436221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499435792819248891624147 8249153689228873337436221)
              ·
                refine ⟨3093432633460827501538583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8249153689228873337436221 3093432633460827501538583)
                ·
                  refine ⟨4640148950191241252307875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093432633460827501538583 4640148950191241252307875)
                  ·
                    refine ⟨6960223425286861878461813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640148950191241252307875 6960223425286861878461813)
                    ·
                      refine ⟨652520946120643301105795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6960223425286861878461813 652520946120643301105795)
                      ·
                        rfl

theorem cell23_1270780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_1270780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270780 prefixEnd_1270780 := by exact prefixLift 1270780
  have htrace : WordTrace (prefixWord ++ tailWord_1270780) baseStart_1270780 baseEnd_1270780 := by
    simpa [prefixWord, tailWord_1270780, baseEnd_1270780] using wordTrace_append hprefix tailTrace_1270780
  have hstable : (prefixWord ++ tailWord_1270780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270780).length < 2 ^ (prefixWord ++ tailWord_1270780).sum := by decide
  have hdescent : baseEnd_1270780 < baseStart_1270780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270803 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_1270803 : Nat := 118140960795 + 1270803 * 2 ^ 59
def prefixEnd_1270803 : Nat := 4983230072969 + 3 ^ 40 * 1270803 * 2
def baseEnd_1270803 : Nat := 652532756175696711118189

theorem tailTrace_1270803 : CollatzResearch.WordTrace tailWord_1270803 prefixEnd_1270803 652532756175696711118189 := by
  unfold tailWord_1270803
  simp only [CollatzResearch.WordTrace]
  refine ⟨46349993215105241718401063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30899995476736827812267375 46349993215105241718401063)
  ·
    refine ⟨69524989822657862577601595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46349993215105241718401063 69524989822657862577601595)
    ·
      refine ⟨104287484733986793866402393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69524989822657862577601595 104287484733986793866402393)
      ·
        refine ⟨78215613550490095399801795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104287484733986793866402393 78215613550490095399801795)
        ·
          refine ⟨117323420325735143099702693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78215613550490095399801795 117323420325735143099702693)
          ·
            refine ⟨21998141311075339331194255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117323420325735143099702693 21998141311075339331194255)
            ·
              refine ⟨32997211966613008996791383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21998141311075339331194255 32997211966613008996791383)
              ·
                refine ⟨49495817949919513495187075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32997211966613008996791383 49495817949919513495187075)
                ·
                  refine ⟨74243726924879270242780613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49495817949919513495187075 74243726924879270242780613)
                  ·
                    refine ⟨13920698798414863170521365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74243726924879270242780613 13920698798414863170521365)
                    ·
                      refine ⟨652532756175696711118189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13920698798414863170521365 652532756175696711118189)
                      ·
                        rfl

theorem cell23_1270803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_1270803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270803 prefixEnd_1270803 := by exact prefixLift 1270803
  have htrace : WordTrace (prefixWord ++ tailWord_1270803) baseStart_1270803 baseEnd_1270803 := by
    simpa [prefixWord, tailWord_1270803, baseEnd_1270803] using wordTrace_append hprefix tailTrace_1270803
  have hstable : (prefixWord ++ tailWord_1270803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270803).length < 2 ^ (prefixWord ++ tailWord_1270803).sum := by decide
  have hdescent : baseEnd_1270803 < baseStart_1270803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270844 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_1270844 : Nat := 118140960795 + 1270844 * 2 ^ 59
def prefixEnd_1270844 : Nat := 4983230072969 + 3 ^ 40 * 1270844 * 2
def baseEnd_1270844 : Nat := 652553808882531050705501

theorem tailTrace_1270844 : CollatzResearch.WordTrace tailWord_1270844 prefixEnd_1270844 652553808882531050705501 := by
  unfold tailWord_1270844
  simp only [CollatzResearch.WordTrace]
  refine ⟨23175744303978352860321793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30900992405304470480429057 23175744303978352860321793)
  ·
    refine ⟨17381808227983764645241345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23175744303978352860321793 17381808227983764645241345)
    ·
      refine ⟨13036356170987823483931009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17381808227983764645241345 13036356170987823483931009)
      ·
        refine ⟨9777267128240867612948257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13036356170987823483931009 9777267128240867612948257)
        ·
          refine ⟨7332950346180650709711193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9777267128240867612948257 7332950346180650709711193)
          ·
            refine ⟨5499712759635488032283395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7332950346180650709711193 5499712759635488032283395)
            ·
              refine ⟨8249569139453232048425093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499712759635488032283395 8249569139453232048425093)
              ·
                refine ⟨1546794213647481009079705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8249569139453232048425093 1546794213647481009079705)
                ·
                  refine ⟨1160095660235610756809779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546794213647481009079705 1160095660235610756809779)
                  ·
                    refine ⟨1740143490353416135214669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160095660235610756809779 1740143490353416135214669)
                    ·
                      refine ⟨652553808882531050705501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740143490353416135214669 652553808882531050705501)
                      ·
                        rfl

theorem cell23_1270844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_1270844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270844 prefixEnd_1270844 := by exact prefixLift 1270844
  have htrace : WordTrace (prefixWord ++ tailWord_1270844) baseStart_1270844 baseEnd_1270844 := by
    simpa [prefixWord, tailWord_1270844, baseEnd_1270844] using wordTrace_append hprefix tailTrace_1270844
  have hstable : (prefixWord ++ tailWord_1270844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270844).length < 2 ^ (prefixWord ++ tailWord_1270844).sum := by decide
  have hdescent : baseEnd_1270844 < baseStart_1270844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270845 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_1270845 : Nat := 118140960795 + 1270845 * 2 ^ 59
def prefixEnd_1270845 : Nat := 4983230072969 + 3 ^ 40 * 1270845 * 2
def baseEnd_1270845 : Nat := 652554322363185546792997

theorem tailTrace_1270845 : CollatzResearch.WordTrace tailWord_1270845 prefixEnd_1270845 652554322363185546792997 := by
  unfold tailWord_1270845
  simp only [CollatzResearch.WordTrace]
  refine ⟨46351525080953082891429989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30901016720635388594286659 46351525080953082891429989)
  ·
    refine ⟨8690910952678703042143123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46351525080953082891429989 8690910952678703042143123)
    ·
      refine ⟨13036366429018054563214685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8690910952678703042143123 13036366429018054563214685)
      ·
        refine ⟨4888637410881770461205507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13036366429018054563214685 4888637410881770461205507)
        ·
          refine ⟨7332956116322655691808261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888637410881770461205507 7332956116322655691808261)
          ·
            refine ⟨1374929271810497942214049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7332956116322655691808261 1374929271810497942214049)
            ·
              refine ⟨1031196953857873456660537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1374929271810497942214049 1031196953857873456660537)
              ·
                refine ⟨773397715393405092495403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031196953857873456660537 773397715393405092495403)
                ·
                  refine ⟨1160096573090107638743105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773397715393405092495403 1160096573090107638743105)
                  ·
                    refine ⟨870072429817580729057329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1160096573090107638743105 870072429817580729057329)
                    ·
                      refine ⟨652554322363185546792997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870072429817580729057329 652554322363185546792997)
                      ·
                        rfl

theorem cell23_1270845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_1270845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270845 prefixEnd_1270845 := by exact prefixLift 1270845
  have htrace : WordTrace (prefixWord ++ tailWord_1270845) baseStart_1270845 baseEnd_1270845 := by
    simpa [prefixWord, tailWord_1270845, baseEnd_1270845] using wordTrace_append hprefix tailTrace_1270845
  have hstable : (prefixWord ++ tailWord_1270845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270845).length < 2 ^ (prefixWord ++ tailWord_1270845).sum := by decide
  have hdescent : baseEnd_1270845 < baseStart_1270845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270861 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1270861 : Nat := 118140960795 + 1270861 * 2 ^ 59
def prefixEnd_1270861 : Nat := 4983230072969 + 3 ^ 40 * 1270861 * 2
def baseEnd_1270861 : Nat := 652562538053657484192923

theorem tailTrace_1270861 : CollatzResearch.WordTrace tailWord_1270861 prefixEnd_1270861 652562538053657484192923 := by
  unfold tailWord_1270861
  simp only [CollatzResearch.WordTrace]
  refine ⟨46352108648895117624012437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30901405765930078416008291 46352108648895117624012437)
  ·
    refine ⟨2172755092916958638625583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46352108648895117624012437 2172755092916958638625583)
    ·
      refine ⟨3259132639375437957938375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172755092916958638625583 3259132639375437957938375)
      ·
        refine ⟨4888698959063156936907563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259132639375437957938375 4888698959063156936907563)
        ·
          refine ⟨7333048438594735405361345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888698959063156936907563 7333048438594735405361345)
          ·
            refine ⟨5499786328946051554021009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7333048438594735405361345 5499786328946051554021009)
            ·
              refine ⟨4124839746709538665515757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499786328946051554021009 4124839746709538665515757)
              ·
                refine ⟨1546814905016076999568409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4124839746709538665515757 1546814905016076999568409)
                ·
                  refine ⟨1160111178762057749676307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546814905016076999568409 1160111178762057749676307)
                  ·
                    refine ⟨1740166768143086624514461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160111178762057749676307 1740166768143086624514461)
                    ·
                      refine ⟨652562538053657484192923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740166768143086624514461 652562538053657484192923)
                      ·
                        rfl

theorem cell23_1270861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1270861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270861 prefixEnd_1270861 := by exact prefixLift 1270861
  have htrace : WordTrace (prefixWord ++ tailWord_1270861) baseStart_1270861 baseEnd_1270861 := by
    simpa [prefixWord, tailWord_1270861, baseEnd_1270861] using wordTrace_append hprefix tailTrace_1270861
  have hstable : (prefixWord ++ tailWord_1270861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270861).length < 2 ^ (prefixWord ++ tailWord_1270861).sum := by decide
  have hdescent : baseEnd_1270861 < baseStart_1270861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270867 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 1, 4, 2]
def baseStart_1270867 : Nat := 118140960795 + 1270867 * 2 ^ 59
def prefixEnd_1270867 : Nat := 4983230072969 + 3 ^ 40 * 1270867 * 2
def baseEnd_1270867 : Nat := 652565618937584460717895

theorem tailTrace_1270867 : CollatzResearch.WordTrace tailWord_1270867 prefixEnd_1270867 652565618937584460717895 := by
  unfold tailWord_1270867
  simp only [CollatzResearch.WordTrace]
  refine ⟨46352327486873380648730855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30901551657915587099153903 46352327486873380648730855)
  ·
    refine ⟨69528491230310070973096283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46352327486873380648730855 69528491230310070973096283)
    ·
      refine ⟨104292736845465106459644425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69528491230310070973096283 104292736845465106459644425)
      ·
        refine ⟨78219552634098829844733319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104292736845465106459644425 78219552634098829844733319)
        ·
          refine ⟨117329328951148244767099979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78219552634098829844733319 117329328951148244767099979)
          ·
            refine ⟨175993993426722367150649969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117329328951148244767099979 175993993426722367150649969)
            ·
              refine ⟨131995495070041775362987477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175993993426722367150649969 131995495070041775362987477)
              ·
                refine ⟨3093644415704104110070019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 131995495070041775362987477 3093644415704104110070019)
                ·
                  refine ⟨4640466623556156165105029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093644415704104110070019 4640466623556156165105029)
                  ·
                    refine ⟨870087491916779280957193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4640466623556156165105029 870087491916779280957193)
                    ·
                      refine ⟨652565618937584460717895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870087491916779280957193 652565618937584460717895)
                      ·
                        rfl

theorem cell23_1270867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4, 2].length) (baseStart_1270867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270867 prefixEnd_1270867 := by exact prefixLift 1270867
  have htrace : WordTrace (prefixWord ++ tailWord_1270867) baseStart_1270867 baseEnd_1270867 := by
    simpa [prefixWord, tailWord_1270867, baseEnd_1270867] using wordTrace_append hprefix tailTrace_1270867
  have hstable : (prefixWord ++ tailWord_1270867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270867).length < 2 ^ (prefixWord ++ tailWord_1270867).sum := by decide
  have hdescent : baseEnd_1270867 < baseStart_1270867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270880 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1270880 : Nat := 118140960795 + 1270880 * 2 ^ 59
def prefixEnd_1270880 : Nat := 4983230072969 + 3 ^ 40 * 1270880 * 2
def baseEnd_1270880 : Nat := 652572294186092909855335

theorem tailTrace_1270880 : CollatzResearch.WordTrace tailWord_1270880 prefixEnd_1270880 652572294186092909855335 := by
  unfold tailWord_1270880
  simp only [CollatzResearch.WordTrace]
  refine ⟨23176400817913141934477047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30901867757217522579302729 23176400817913141934477047)
  ·
    refine ⟨34764601226869712901715571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23176400817913141934477047 34764601226869712901715571)
    ·
      refine ⟨52146901840304569352573357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34764601226869712901715571 52146901840304569352573357)
      ·
        refine ⟨19555088190114213507215009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52146901840304569352573357 19555088190114213507215009)
        ·
          refine ⟨14666316142585660130411257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19555088190114213507215009 14666316142585660130411257)
          ·
            refine ⟨10999737106939245097808443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14666316142585660130411257 10999737106939245097808443)
            ·
              refine ⟨16499605660408867646712665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10999737106939245097808443 16499605660408867646712665)
              ·
                refine ⟨12374704245306650735034499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16499605660408867646712665 12374704245306650735034499)
                ·
                  refine ⟨18562056367959976102551749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12374704245306650735034499 18562056367959976102551749)
                  ·
                    refine ⟨3480385568992495519228453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18562056367959976102551749 3480385568992495519228453)
                    ·
                      refine ⟨652572294186092909855335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3480385568992495519228453 652572294186092909855335)
                      ·
                        rfl

theorem cell23_1270880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1270880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270880 prefixEnd_1270880 := by exact prefixLift 1270880
  have htrace : WordTrace (prefixWord ++ tailWord_1270880) baseStart_1270880 baseEnd_1270880 := by
    simpa [prefixWord, tailWord_1270880, baseEnd_1270880] using wordTrace_append hprefix tailTrace_1270880
  have hstable : (prefixWord ++ tailWord_1270880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270880).length < 2 ^ (prefixWord ++ tailWord_1270880).sum := by decide
  have hdescent : baseEnd_1270880 < baseStart_1270880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270884 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_1270884 : Nat := 118140960795 + 1270884 * 2 ^ 59
def prefixEnd_1270884 : Nat := 4983230072969 + 3 ^ 40 * 1270884 * 2
def baseEnd_1270884 : Nat := 652574348108710894205317

theorem tailTrace_1270884 : CollatzResearch.WordTrace tailWord_1270884 prefixEnd_1270884 652574348108710894205317 := by
  unfold tailWord_1270884
  simp only [CollatzResearch.WordTrace]
  refine ⟨23176473763905896276049853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30901965018541195034733137 23176473763905896276049853)
  ·
    refine ⟨8691177661464711103518695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23176473763905896276049853 8691177661464711103518695)
    ·
      refine ⟨13036766492197066655278043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8691177661464711103518695 13036766492197066655278043)
      ·
        refine ⟨19555149738295599982917065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036766492197066655278043 19555149738295599982917065)
        ·
          refine ⟨14666362303721699987187799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19555149738295599982917065 14666362303721699987187799)
          ·
            refine ⟨21999543455582549980781699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14666362303721699987187799 21999543455582549980781699)
            ·
              refine ⟨32999315183373824971172549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21999543455582549980781699 32999315183373824971172549)
              ·
                refine ⟨6187371596882592182094853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32999315183373824971172549 6187371596882592182094853)
                ·
                  refine ⟨1160132174415486034142785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6187371596882592182094853 1160132174415486034142785)
                  ·
                    refine ⟨870099130811614525607089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1160132174415486034142785 870099130811614525607089)
                    ·
                      refine ⟨652574348108710894205317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870099130811614525607089 652574348108710894205317)
                      ·
                        rfl

theorem cell23_1270884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_1270884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270884 prefixEnd_1270884 := by exact prefixLift 1270884
  have htrace : WordTrace (prefixWord ++ tailWord_1270884) baseStart_1270884 baseEnd_1270884 := by
    simpa [prefixWord, tailWord_1270884, baseEnd_1270884] using wordTrace_append hprefix tailTrace_1270884
  have hstable : (prefixWord ++ tailWord_1270884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270884).length < 2 ^ (prefixWord ++ tailWord_1270884).sum := by decide
  have hdescent : baseEnd_1270884 < baseStart_1270884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270888 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1270888 : Nat := 118140960795 + 1270888 * 2 ^ 59
def prefixEnd_1270888 : Nat := 4983230072969 + 3 ^ 40 * 1270888 * 2
def baseEnd_1270888 : Nat := 652576402031328878555299

theorem tailTrace_1270888 : CollatzResearch.WordTrace tailWord_1270888 prefixEnd_1270888 652576402031328878555299 := by
  unfold tailWord_1270888
  simp only [CollatzResearch.WordTrace]
  refine ⟨23176546709898650617622659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30902062279864867490163545 23176546709898650617622659)
  ·
    refine ⟨34764820064847975926433989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23176546709898650617622659 34764820064847975926433989)
    ·
      refine ⟨6518403762158995486206373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34764820064847975926433989 6518403762158995486206373)
      ·
        refine ⟨1222200705404811653663695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6518403762158995486206373 1222200705404811653663695)
        ·
          refine ⟨1833301058107217480495543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222200705404811653663695 1833301058107217480495543)
          ·
            refine ⟨2749951587160826220743315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833301058107217480495543 2749951587160826220743315)
            ·
              refine ⟨4124927380741239331114973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749951587160826220743315 4124927380741239331114973)
              ·
                refine ⟨1546847767777964749168115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4124927380741239331114973 1546847767777964749168115)
                ·
                  refine ⟨2320271651666947123752173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546847767777964749168115 2320271651666947123752173)
                  ·
                    refine ⟨870101869375105171407065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320271651666947123752173 870101869375105171407065)
                    ·
                      refine ⟨652576402031328878555299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870101869375105171407065 652576402031328878555299)
                      ·
                        rfl

theorem cell23_1270888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1270888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270888 prefixEnd_1270888 := by exact prefixLift 1270888
  have htrace : WordTrace (prefixWord ++ tailWord_1270888) baseStart_1270888 baseEnd_1270888 := by
    simpa [prefixWord, tailWord_1270888, baseEnd_1270888] using wordTrace_append hprefix tailTrace_1270888
  have hstable : (prefixWord ++ tailWord_1270888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270888).length < 2 ^ (prefixWord ++ tailWord_1270888).sum := by decide
  have hdescent : baseEnd_1270888 < baseStart_1270888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270954 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1270954 : Nat := 118140960795 + 1270954 * 2 ^ 59
def prefixEnd_1270954 : Nat := 4983230072969 + 3 ^ 40 * 1270954 * 2
def baseEnd_1270954 : Nat := 217536763918175206776665

theorem tailTrace_1270954 : CollatzResearch.WordTrace tailWord_1270954 prefixEnd_1270954 217536763918175206776665 := by
  unfold tailWord_1270954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588875159389548626786979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30903667091705463004765277 11588875159389548626786979)
  ·
    refine ⟨17383312739084322940180469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11588875159389548626786979 17383312739084322940180469)
    ·
      refine ⟨1629685569289155275641919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17383312739084322940180469 1629685569289155275641919)
      ·
        refine ⟨2444528353933732913462879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629685569289155275641919 2444528353933732913462879)
        ·
          refine ⟨3666792530900599370194319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444528353933732913462879 3666792530900599370194319)
          ·
            refine ⟨5500188796350899055291479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666792530900599370194319 5500188796350899055291479)
            ·
              refine ⟨8250283194526348582937219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500188796350899055291479 8250283194526348582937219)
              ·
                refine ⟨12375424791789522874405829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250283194526348582937219 12375424791789522874405829)
                ·
                  refine ⟨2320392148460535538951093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12375424791789522874405829 2320392148460535538951093)
                  ·
                    refine ⟨217536763918175206776665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2320392148460535538951093 217536763918175206776665)
                    ·
                      rfl

theorem cell23_1270954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1270954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270954 prefixEnd_1270954 := by exact prefixLift 1270954
  have htrace : WordTrace (prefixWord ++ tailWord_1270954) baseStart_1270954 baseEnd_1270954 := by
    simpa [prefixWord, tailWord_1270954, baseEnd_1270954] using wordTrace_append hprefix tailTrace_1270954
  have hstable : (prefixWord ++ tailWord_1270954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270954).length < 2 ^ (prefixWord ++ tailWord_1270954).sum := by decide
  have hdescent : baseEnd_1270954 < baseStart_1270954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270960 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_1270960 : Nat := 118140960795 + 1270960 * 2 ^ 59
def prefixEnd_1270960 : Nat := 4983230072969 + 3 ^ 40 * 1270960 * 2
def baseEnd_1270960 : Nat := 652613372638452596854967

theorem tailTrace_1270960 : CollatzResearch.WordTrace tailWord_1270960 prefixEnd_1270960 652613372638452596854967 := by
  unfold tailWord_1270960
  simp only [CollatzResearch.WordTrace]
  refine ⟨23177859737768228765933167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30903812983690971687910889 23177859737768228765933167)
  ·
    refine ⟨34766789606652343148899751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23177859737768228765933167 34766789606652343148899751)
    ·
      refine ⟨52150184409978514723349627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34766789606652343148899751 52150184409978514723349627)
      ·
        refine ⟨78225276614967772085024441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52150184409978514723349627 78225276614967772085024441)
        ·
          refine ⟨58668957461225829063768331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78225276614967772085024441 58668957461225829063768331)
          ·
            refine ⟨88003436191838743595652497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58668957461225829063768331 88003436191838743595652497)
            ·
              refine ⟨66002577143879057696739373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88003436191838743595652497 66002577143879057696739373)
              ·
                refine ⟨24750966428954646636277265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66002577143879057696739373 24750966428954646636277265)
                ·
                  refine ⟨18563224821715984977207949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24750966428954646636277265 18563224821715984977207949)
                  ·
                    refine ⟨6961209308143494366452981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18563224821715984977207949 6961209308143494366452981)
                    ·
                      refine ⟨652613372638452596854967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6961209308143494366452981 652613372638452596854967)
                      ·
                        rfl

theorem cell23_1270960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_1270960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1270960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1270960 prefixEnd_1270960 := by exact prefixLift 1270960
  have htrace : WordTrace (prefixWord ++ tailWord_1270960) baseStart_1270960 baseEnd_1270960 := by
    simpa [prefixWord, tailWord_1270960, baseEnd_1270960] using wordTrace_append hprefix tailTrace_1270960
  have hstable : (prefixWord ++ tailWord_1270960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270960).length < 2 ^ (prefixWord ++ tailWord_1270960).sum := by decide
  have hdescent : baseEnd_1270960 < baseStart_1270960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271018 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1271018 : Nat := 118140960795 + 1271018 * 2 ^ 59
def prefixEnd_1271018 : Nat := 4983230072969 + 3 ^ 40 * 1271018 * 2
def baseEnd_1271018 : Nat := 217547718172137789976567

theorem tailTrace_1271018 : CollatzResearch.WordTrace tailWord_1271018 prefixEnd_1271018 217547718172137789976567 := by
  unfold tailWord_1271018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11589458727331583359369427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30905223272884222291651805 11589458727331583359369427)
  ·
    refine ⟨17384188090997375039054141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11589458727331583359369427 17384188090997375039054141)
    ·
      refine ⟨6519070534124015639645303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17384188090997375039054141 6519070534124015639645303)
      ·
        refine ⟨9778605801186023459467955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519070534124015639645303 9778605801186023459467955)
        ·
          refine ⟨14667908701779035189201933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9778605801186023459467955 14667908701779035189201933)
          ·
            refine ⟨5500465763167138195950725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14667908701779035189201933 5500465763167138195950725)
            ·
              refine ⟨1031337330593838411740761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5500465763167138195950725 1031337330593838411740761)
              ·
                refine ⟨773502997945378808805571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031337330593838411740761 773502997945378808805571)
                ·
                  refine ⟨1160254496918068213208357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773502997945378808805571 1160254496918068213208357)
                  ·
                    refine ⟨217547718172137789976567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160254496918068213208357 217547718172137789976567)
                    ·
                      rfl

theorem cell23_1271018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1271018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271018 prefixEnd_1271018 := by exact prefixLift 1271018
  have htrace : WordTrace (prefixWord ++ tailWord_1271018) baseStart_1271018 baseEnd_1271018 := by
    simpa [prefixWord, tailWord_1271018, baseEnd_1271018] using wordTrace_append hprefix tailTrace_1271018
  have hstable : (prefixWord ++ tailWord_1271018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271018).length < 2 ^ (prefixWord ++ tailWord_1271018).sum := by decide
  have hdescent : baseEnd_1271018 < baseStart_1271018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271027 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 3, 5]
def baseStart_1271027 : Nat := 118140960795 + 1271027 * 2 ^ 59
def prefixEnd_1271027 : Nat := 4983230072969 + 3 ^ 40 * 1271027 * 2
def baseEnd_1271027 : Nat := 217549258614101278239053

theorem tailTrace_1271027 : CollatzResearch.WordTrace tailWord_1271027 prefixEnd_1271027 217549258614101278239053 := by
  unfold tailWord_1271027
  simp only [CollatzResearch.WordTrace]
  refine ⟨46358163166293727974555335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30905442110862485316370223 46358163166293727974555335)
  ·
    refine ⟨69537244749440591961833003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46358163166293727974555335 69537244749440591961833003)
    ·
      refine ⟨104305867124160887942749505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69537244749440591961833003 104305867124160887942749505)
      ·
        refine ⟨78229400343120665957062129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104305867124160887942749505 78229400343120665957062129)
        ·
          refine ⟨58672050257340499467796597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78229400343120665957062129 58672050257340499467796597)
          ·
            refine ⟨5500504711625671825105931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58672050257340499467796597 5500504711625671825105931)
            ·
              refine ⟨8250757067438507737658897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500504711625671825105931 8250757067438507737658897)
              ·
                refine ⟨6188067800578880803244173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8250757067438507737658897 6188067800578880803244173)
                ·
                  refine ⟨2320525425217080301216565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6188067800578880803244173 2320525425217080301216565)
                  ·
                    refine ⟨217549258614101278239053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2320525425217080301216565 217549258614101278239053)
                    ·
                      rfl

theorem cell23_1271027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 5].length) (baseStart_1271027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271027 prefixEnd_1271027 := by exact prefixLift 1271027
  have htrace : WordTrace (prefixWord ++ tailWord_1271027) baseStart_1271027 baseEnd_1271027 := by
    simpa [prefixWord, tailWord_1271027, baseEnd_1271027] using wordTrace_append hprefix tailTrace_1271027
  have hstable : (prefixWord ++ tailWord_1271027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271027).length < 2 ^ (prefixWord ++ tailWord_1271027).sum := by decide
  have hdescent : baseEnd_1271027 < baseStart_1271027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271034 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2]
def baseStart_1271034 : Nat := 118140960795 + 1271034 * 2 ^ 59
def prefixEnd_1271034 : Nat := 4983230072969 + 3 ^ 40 * 1271034 * 2
def baseEnd_1271034 : Nat := 652651370206885307329627

theorem tailTrace_1271034 : CollatzResearch.WordTrace tailWord_1271034 prefixEnd_1271034 652651370206885307329627 := by
  unfold tailWord_1271034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11589604619317092042515039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30905612318178912113373437 11589604619317092042515039)
  ·
    refine ⟨17384406928975638063772559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11589604619317092042515039 17384406928975638063772559)
    ·
      refine ⟨26076610393463457095658839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17384406928975638063772559 26076610393463457095658839)
      ·
        refine ⟨39114915590195185643488259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26076610393463457095658839 39114915590195185643488259)
        ·
          refine ⟨58672373385292778465232389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39114915590195185643488259 58672373385292778465232389)
          ·
            refine ⟨11001070009742395962231073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58672373385292778465232389 11001070009742395962231073)
            ·
              refine ⟨8250802507306796971673305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11001070009742395962231073 8250802507306796971673305)
              ·
                refine ⟨6188101880480097728754979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8250802507306796971673305 6188101880480097728754979)
                ·
                  refine ⟨9282152820720146593132469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6188101880480097728754979 9282152820720146593132469)
                  ·
                    refine ⟨870201826942513743106169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9282152820720146593132469 870201826942513743106169)
                    ·
                      refine ⟨652651370206885307329627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870201826942513743106169 652651370206885307329627)
                      ·
                        rfl

theorem cell23_1271034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_1271034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271034 prefixEnd_1271034 := by exact prefixLift 1271034
  have htrace : WordTrace (prefixWord ++ tailWord_1271034) baseStart_1271034 baseEnd_1271034 := by
    simpa [prefixWord, tailWord_1271034, baseEnd_1271034] using wordTrace_append hprefix tailTrace_1271034
  have hstable : (prefixWord ++ tailWord_1271034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271034).length < 2 ^ (prefixWord ++ tailWord_1271034).sum := by decide
  have hdescent : baseEnd_1271034 < baseStart_1271034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271041 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1271041 : Nat := 118140960795 + 1271041 * 2 ^ 59
def prefixEnd_1271041 : Nat := 4983230072969 + 3 ^ 40 * 1271041 * 2
def baseEnd_1271041 : Nat := 652654964571466779942095

theorem tailTrace_1271041 : CollatzResearch.WordTrace tailWord_1271041 prefixEnd_1271041 652654964571466779942095 := by
  unfold tailWord_1271041
  simp only [CollatzResearch.WordTrace]
  refine ⟨46358673788243008365564977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30905782525495338910376651 46358673788243008365564977)
  ·
    refine ⟨34769005341182256274173733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46358673788243008365564977 34769005341182256274173733)
    ·
      refine ⟨6519188501471673051407575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34769005341182256274173733 6519188501471673051407575)
      ·
        refine ⟨9778782752207509577111363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519188501471673051407575 9778782752207509577111363)
        ·
          refine ⟨14668174128311264365667045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9778782752207509577111363 14668174128311264365667045)
          ·
            refine ⟨2750282649058362068562571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14668174128311264365667045 2750282649058362068562571)
            ·
              refine ⟨4125423973587543102843857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750282649058362068562571 4125423973587543102843857)
              ·
                refine ⟨3094067980190657327132893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4125423973587543102843857 3094067980190657327132893)
                ·
                  refine ⟨1160275492571496497674835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3094067980190657327132893 1160275492571496497674835)
                  ·
                    refine ⟨1740413238857244746512253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160275492571496497674835 1740413238857244746512253)
                    ·
                      refine ⟨652654964571466779942095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740413238857244746512253 652654964571466779942095)
                      ·
                        rfl

theorem cell23_1271041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1271041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271041 prefixEnd_1271041 := by exact prefixLift 1271041
  have htrace : WordTrace (prefixWord ++ tailWord_1271041) baseStart_1271041 baseEnd_1271041 := by
    simpa [prefixWord, tailWord_1271041, baseEnd_1271041] using wordTrace_append hprefix tailTrace_1271041
  have hstable : (prefixWord ++ tailWord_1271041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271041).length < 2 ^ (prefixWord ++ tailWord_1271041).sum := by decide
  have hdescent : baseEnd_1271041 < baseStart_1271041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271044 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1271044 : Nat := 118140960795 + 1271044 * 2 ^ 59
def prefixEnd_1271044 : Nat := 4983230072969 + 3 ^ 40 * 1271044 * 2
def baseEnd_1271044 : Nat := 217552168337810089401527

theorem tailTrace_1271044 : CollatzResearch.WordTrace tailWord_1271044 prefixEnd_1271044 217552168337810089401527 := by
  unfold tailWord_1271044
  simp only [CollatzResearch.WordTrace]
  refine ⟨23179391603616069938962093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30905855471488093251949457 23179391603616069938962093)
  ·
    refine ⟨8692271851356026227110785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23179391603616069938962093 8692271851356026227110785)
    ·
      refine ⟨6519203888517019670333089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8692271851356026227110785 6519203888517019670333089)
      ·
        refine ⟨4889402916387764752749817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6519203888517019670333089 4889402916387764752749817)
        ·
          refine ⟨3667052187290823564562363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889402916387764752749817 3667052187290823564562363)
          ·
            refine ⟨5500578280936235346843545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667052187290823564562363 5500578280936235346843545)
            ·
              refine ⟨4125433710702176510132659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500578280936235346843545 4125433710702176510132659)
              ·
                refine ⟨6188150566053264765198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125433710702176510132659 6188150566053264765198989)
                ·
                  refine ⟨2320556462269974286949621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6188150566053264765198989 2320556462269974286949621)
                  ·
                    refine ⟨217552168337810089401527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2320556462269974286949621 217552168337810089401527)
                    ·
                      rfl

theorem cell23_1271044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1271044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271044 prefixEnd_1271044 := by exact prefixLift 1271044
  have htrace : WordTrace (prefixWord ++ tailWord_1271044) baseStart_1271044 baseEnd_1271044 := by
    simpa [prefixWord, tailWord_1271044, baseEnd_1271044] using wordTrace_append hprefix tailTrace_1271044
  have hstable : (prefixWord ++ tailWord_1271044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271044).length < 2 ^ (prefixWord ++ tailWord_1271044).sum := by decide
  have hdescent : baseEnd_1271044 < baseStart_1271044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271051 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 2, 3, 2]
def baseStart_1271051 : Nat := 118140960795 + 1271051 * 2 ^ 59
def prefixEnd_1271051 : Nat := 4983230072969 + 3 ^ 40 * 1271051 * 2
def baseEnd_1271051 : Nat := 652660099378011740817049

theorem tailTrace_1271051 : CollatzResearch.WordTrace tailWord_1271051 prefixEnd_1271051 652660099378011740817049 := by
  unfold tailWord_1271051
  simp only [CollatzResearch.WordTrace]
  refine ⟨46359038518206780073429007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30906025678804520048952671 46359038518206780073429007)
  ·
    refine ⟨69538557777310170110143511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46359038518206780073429007 69538557777310170110143511)
    ·
      refine ⟨104307836665965255165215267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69538557777310170110143511 104307836665965255165215267)
      ·
        refine ⟨156461754998947882747822901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104307836665965255165215267 156461754998947882747822901)
        ·
          refine ⟨14668289531151364007608397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156461754998947882747822901 14668289531151364007608397)
          ·
            refine ⟨5500608574181761502853149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14668289531151364007608397 5500608574181761502853149)
            ·
              refine ⟨2062728215318160563569931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5500608574181761502853149 2062728215318160563569931)
              ·
                refine ⟨3094092322977240845354897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062728215318160563569931 3094092322977240845354897)
                ·
                  refine ⟨2320569242232930634016173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094092322977240845354897 2320569242232930634016173)
                  ·
                    refine ⟨870213465837348987756065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320569242232930634016173 870213465837348987756065)
                    ·
                      refine ⟨652660099378011740817049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870213465837348987756065 652660099378011740817049)
                      ·
                        rfl

theorem cell23_1271051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3, 2].length) (baseStart_1271051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271051 prefixEnd_1271051 := by exact prefixLift 1271051
  have htrace : WordTrace (prefixWord ++ tailWord_1271051) baseStart_1271051 baseEnd_1271051 := by
    simpa [prefixWord, tailWord_1271051, baseEnd_1271051] using wordTrace_append hprefix tailTrace_1271051
  have hstable : (prefixWord ++ tailWord_1271051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271051).length < 2 ^ (prefixWord ++ tailWord_1271051).sum := by decide
  have hdescent : baseEnd_1271051 < baseStart_1271051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271057 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_1271057 : Nat := 118140960795 + 1271057 * 2 ^ 59
def prefixEnd_1271057 : Nat := 4983230072969 + 3 ^ 40 * 1271057 * 2
def baseEnd_1271057 : Nat := 217554393420646239114007

theorem tailTrace_1271057 : CollatzResearch.WordTrace tailWord_1271057 prefixEnd_1271057 217554393420646239114007 := by
  unfold tailWord_1271057
  simp only [CollatzResearch.WordTrace]
  refine ⟨46359257356185043098147425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30906171570790028732098283 46359257356185043098147425)
  ·
    refine ⟨34769443017138782323610569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46359257356185043098147425 34769443017138782323610569)
    ·
      refine ⟨26077082262854086742707927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34769443017138782323610569 26077082262854086742707927)
      ·
        refine ⟨39115623394281130114061891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26077082262854086742707927 39115623394281130114061891)
        ·
          refine ⟨58673435091421695171092837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39115623394281130114061891 58673435091421695171092837)
          ·
            refine ⟨11001269079641567844579907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58673435091421695171092837 11001269079641567844579907)
            ·
              refine ⟨16501903619462351766869861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11001269079641567844579907 16501903619462351766869861)
              ·
                refine ⟨3094106928649190956288099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16501903619462351766869861 3094106928649190956288099)
                ·
                  refine ⟨4641160392973786434432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094106928649190956288099 4641160392973786434432149)
                  ·
                    refine ⟨217554393420646239114007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4641160392973786434432149 217554393420646239114007)
                    ·
                      rfl

theorem cell23_1271057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_1271057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271057 prefixEnd_1271057 := by exact prefixLift 1271057
  have htrace : WordTrace (prefixWord ++ tailWord_1271057) baseStart_1271057 baseEnd_1271057 := by
    simpa [prefixWord, tailWord_1271057, baseEnd_1271057] using wordTrace_append hprefix tailTrace_1271057
  have hstable : (prefixWord ++ tailWord_1271057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271057).length < 2 ^ (prefixWord ++ tailWord_1271057).sum := by decide
  have hdescent : baseEnd_1271057 < baseStart_1271057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271067 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5]
def baseStart_1271067 : Nat := 118140960795 + 1271067 * 2 ^ 59
def prefixEnd_1271067 : Nat := 4983230072969 + 3 ^ 40 * 1271067 * 2
def baseEnd_1271067 : Nat := 652668315068483678216975

theorem tailTrace_1271067 : CollatzResearch.WordTrace tailWord_1271067 prefixEnd_1271067 652668315068483678216975 := by
  unfold tailWord_1271067
  simp only [CollatzResearch.WordTrace]
  refine ⟨46359622086148814806011455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30906414724099209870674303 46359622086148814806011455)
  ·
    refine ⟨69539433129223222209017183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46359622086148814806011455 69539433129223222209017183)
    ·
      refine ⟨104309149693834833313525775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69539433129223222209017183 104309149693834833313525775)
      ·
        refine ⟨156463724540752249970288663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104309149693834833313525775 156463724540752249970288663)
        ·
          refine ⟨234695586811128374955432995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156463724540752249970288663 234695586811128374955432995)
          ·
            refine ⟨352043380216692562433149493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234695586811128374955432995 352043380216692562433149493)
            ·
              refine ⟨33004066895314927728107765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352043380216692562433149493 33004066895314927728107765)
              ·
                refine ⟨3094131271435774474510103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33004066895314927728107765 3094131271435774474510103)
                ·
                  refine ⟨4641196907153661711765155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094131271435774474510103 4641196907153661711765155)
                  ·
                    refine ⟨6961795360730492567647733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641196907153661711765155 6961795360730492567647733)
                    ·
                      refine ⟨652668315068483678216975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6961795360730492567647733 652668315068483678216975)
                      ·
                        rfl

theorem cell23_1271067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 5].length) (baseStart_1271067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271067 prefixEnd_1271067 := by exact prefixLift 1271067
  have htrace : WordTrace (prefixWord ++ tailWord_1271067) baseStart_1271067 baseEnd_1271067 := by
    simpa [prefixWord, tailWord_1271067, baseEnd_1271067] using wordTrace_append hprefix tailTrace_1271067
  have hstable : (prefixWord ++ tailWord_1271067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271067).length < 2 ^ (prefixWord ++ tailWord_1271067).sum := by decide
  have hdescent : baseEnd_1271067 < baseStart_1271067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271114 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1271114 : Nat := 118140960795 + 1271114 * 2 ^ 59
def prefixEnd_1271114 : Nat := 4983230072969 + 3 ^ 40 * 1271114 * 2
def baseEnd_1271114 : Nat := 652692448659244994329259

theorem tailTrace_1271114 : CollatzResearch.WordTrace tailWord_1271114 prefixEnd_1271114 652692448659244994329259 := by
  unfold tailWord_1271114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590334079244635458243099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30907557544652361221981597 11590334079244635458243099)
  ·
    refine ⟨17385501118866953187364649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11590334079244635458243099 17385501118866953187364649)
    ·
      refine ⟨13039125839150214890523487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17385501118866953187364649 13039125839150214890523487)
      ·
        refine ⟨19558688758725322335785231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13039125839150214890523487 19558688758725322335785231)
        ·
          refine ⟨29338033138087983503677847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19558688758725322335785231 29338033138087983503677847)
          ·
            refine ⟨44007049707131975255516771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29338033138087983503677847 44007049707131975255516771)
            ·
              refine ⟨66010574560697962883275157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44007049707131975255516771 66010574560697962883275157)
              ·
                refine ⟨3094245682532717010153523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66010574560697962883275157 3094245682532717010153523)
                ·
                  refine ⟨4641368523799075515230285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094245682532717010153523 4641368523799075515230285)
                  ·
                    refine ⟨1740513196424653318211357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4641368523799075515230285 1740513196424653318211357)
                    ·
                      refine ⟨652692448659244994329259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740513196424653318211357 652692448659244994329259)
                      ·
                        rfl

theorem cell23_1271114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1271114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271114 prefixEnd_1271114 := by exact prefixLift 1271114
  have htrace : WordTrace (prefixWord ++ tailWord_1271114) baseStart_1271114 baseEnd_1271114 := by
    simpa [prefixWord, tailWord_1271114, baseEnd_1271114] using wordTrace_append hprefix tailTrace_1271114
  have hstable : (prefixWord ++ tailWord_1271114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271114).length < 2 ^ (prefixWord ++ tailWord_1271114).sum := by decide
  have hdescent : baseEnd_1271114 < baseStart_1271114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271126 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1271126 : Nat := 118140960795 + 1271126 * 2 ^ 59
def prefixEnd_1271126 : Nat := 4983230072969 + 3 ^ 40 * 1271126 * 2
def baseEnd_1271126 : Nat := 652698610427098947379205

theorem tailTrace_1271126 : CollatzResearch.WordTrace tailWord_1271126 prefixEnd_1271126 652698610427098947379205 := by
  unfold tailWord_1271126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897610874558441742650577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30907849328623378588272821 2897610874558441742650577)
  ·
    refine ⟨2173208155918831306987933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897610874558441742650577 2173208155918831306987933)
    ·
      refine ⟨814953058469561740120475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2173208155918831306987933 814953058469561740120475)
      ·
        refine ⟨1222429587704342610180713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814953058469561740120475 1222429587704342610180713)
        ·
          refine ⟨916822190778256957635535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222429587704342610180713 916822190778256957635535)
          ·
            refine ⟨1375233286167385436453303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916822190778256957635535 1375233286167385436453303)
            ·
              refine ⟨2062849929251078154679955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375233286167385436453303 2062849929251078154679955)
              ·
                refine ⟨3094274893876617232019933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062849929251078154679955 3094274893876617232019933)
                ·
                  refine ⟨1160353085203731462007475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3094274893876617232019933 1160353085203731462007475)
                  ·
                    refine ⟨1740529627805597193011213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160353085203731462007475 1740529627805597193011213)
                    ·
                      refine ⟨652698610427098947379205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740529627805597193011213 652698610427098947379205)
                      ·
                        rfl

theorem cell23_1271126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1271126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271126 prefixEnd_1271126 := by exact prefixLift 1271126
  have htrace : WordTrace (prefixWord ++ tailWord_1271126) baseStart_1271126 baseEnd_1271126 := by
    simpa [prefixWord, tailWord_1271126, baseEnd_1271126] using wordTrace_append hprefix tailTrace_1271126
  have hstable : (prefixWord ++ tailWord_1271126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271126).length < 2 ^ (prefixWord ++ tailWord_1271126).sum := by decide
  have hdescent : baseEnd_1271126 < baseStart_1271126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271141 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 3, 3, 2]
def baseStart_1271141 : Nat := 118140960795 + 1271141 * 2 ^ 59
def prefixEnd_1271141 : Nat := 4983230072969 + 3 ^ 40 * 1271141 * 2
def baseEnd_1271141 : Nat := 652706312636916388691635

theorem tailTrace_1271141 : CollatzResearch.WordTrace tailWord_1271141 prefixEnd_1271141 652706312636916388691635 := by
  unfold tailWord_1271141
  simp only [CollatzResearch.WordTrace]
  refine ⟨46362321087880725444205277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30908214058587150296136851 46362321087880725444205277)
  ·
    refine ⟨17385870407955272041576979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46362321087880725444205277 17385870407955272041576979)
    ·
      refine ⟨26078805611932908062365469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17385870407955272041576979 26078805611932908062365469)
      ·
        refine ⟨9779552104474840523387051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26078805611932908062365469 9779552104474840523387051)
        ·
          refine ⟨14669328156712260785080577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9779552104474840523387051 14669328156712260785080577)
          ·
            refine ⟨11001996117534195588810433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14669328156712260785080577 11001996117534195588810433)
            ·
              refine ⟨8251497088150646691607825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11001996117534195588810433 8251497088150646691607825)
              ·
                refine ⟨6188622816112985018705869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8251497088150646691607825 6188622816112985018705869)
                ·
                  refine ⟨2320733556042369382014701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6188622816112985018705869 2320733556042369382014701)
                  ·
                    refine ⟨870275083515888518255513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320733556042369382014701 870275083515888518255513)
                    ·
                      refine ⟨652706312636916388691635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870275083515888518255513 652706312636916388691635)
                      ·
                        rfl

theorem cell23_1271141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_1271141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271141 prefixEnd_1271141 := by exact prefixLift 1271141
  have htrace : WordTrace (prefixWord ++ tailWord_1271141) baseStart_1271141 baseEnd_1271141 := by
    simpa [prefixWord, tailWord_1271141, baseEnd_1271141] using wordTrace_append hprefix tailTrace_1271141
  have hstable : (prefixWord ++ tailWord_1271141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271141).length < 2 ^ (prefixWord ++ tailWord_1271141).sum := by decide
  have hdescent : baseEnd_1271141 < baseStart_1271141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271148 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_1271148 : Nat := 118140960795 + 1271148 * 2 ^ 59
def prefixEnd_1271148 : Nat := 4983230072969 + 3 ^ 40 * 1271148 * 2
def baseEnd_1271148 : Nat := 652709907001497861304103

theorem tailTrace_1271148 : CollatzResearch.WordTrace tailWord_1271148 prefixEnd_1271148 652709907001497861304103 := by
  unfold tailWord_1271148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23181288199427682819855049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30908384265903577093140065 23181288199427682819855049)
  ·
    refine ⟨17385966149570762114891287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23181288199427682819855049 17385966149570762114891287)
    ·
      refine ⟨26078949224356143172336931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17385966149570762114891287 26078949224356143172336931)
      ·
        refine ⟨39118423836534214758505397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26078949224356143172336931 39118423836534214758505397)
        ·
          refine ⟨3667352234675082633609881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39118423836534214758505397 3667352234675082633609881)
          ·
            refine ⟨2750514176006311975207411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3667352234675082633609881 2750514176006311975207411)
            ·
              refine ⟨4125771264009467962811117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750514176006311975207411 4125771264009467962811117)
              ·
                refine ⟨1547164224003550486054169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4125771264009467962811117 1547164224003550486054169)
                ·
                  refine ⟨1160373168002662864540627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1547164224003550486054169 1160373168002662864540627)
                  ·
                    refine ⟨1740559752003994296810941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160373168002662864540627 1740559752003994296810941)
                    ·
                      refine ⟨652709907001497861304103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740559752003994296810941 652709907001497861304103)
                      ·
                        rfl

theorem cell23_1271148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_1271148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271148 prefixEnd_1271148 := by exact prefixLift 1271148
  have htrace : WordTrace (prefixWord ++ tailWord_1271148) baseStart_1271148 baseEnd_1271148 := by
    simpa [prefixWord, tailWord_1271148, baseEnd_1271148] using wordTrace_append hprefix tailTrace_1271148
  have hstable : (prefixWord ++ tailWord_1271148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271148).length < 2 ^ (prefixWord ++ tailWord_1271148).sum := by decide
  have hdescent : baseEnd_1271148 < baseStart_1271148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271171 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 3, 4, 2]
def baseStart_1271171 : Nat := 118140960795 + 1271171 * 2 ^ 59
def prefixEnd_1271171 : Nat := 4983230072969 + 3 ^ 40 * 1271171 * 2
def baseEnd_1271171 : Nat := 652721717056551271316497

theorem tailTrace_1271171 : CollatzResearch.WordTrace tailWord_1271171 prefixEnd_1271171 652721717056551271316497 := by
  unfold tailWord_1271171
  simp only [CollatzResearch.WordTrace]
  refine ⟨46363415277772040567797367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30908943518514693711864911 46363415277772040567797367)
  ·
    refine ⟨69545122916658060851696051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46363415277772040567797367 69545122916658060851696051)
    ·
      refine ⟨104317684374987091277544077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69545122916658060851696051 104317684374987091277544077)
      ·
        refine ⟨39119131640620159229079029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104317684374987091277544077 39119131640620159229079029)
        ·
          refine ⟨3667418591308139927726159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39119131640620159229079029 3667418591308139927726159)
          ·
            refine ⟨5501127886962209891589239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667418591308139927726159 5501127886962209891589239)
            ·
              refine ⟨8251691830443314837383859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501127886962209891589239 8251691830443314837383859)
              ·
                refine ⟨12377537745664972256075789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8251691830443314837383859 12377537745664972256075789)
                ·
                  refine ⟨4641576654624364596028421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12377537745664972256075789 4641576654624364596028421)
                  ·
                    refine ⟨870295622742068361755329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4641576654624364596028421 870295622742068361755329)
                    ·
                      refine ⟨652721717056551271316497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870295622742068361755329 652721717056551271316497)
                      ·
                        rfl

theorem cell23_1271171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4, 2].length) (baseStart_1271171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271171 prefixEnd_1271171 := by exact prefixLift 1271171
  have htrace : WordTrace (prefixWord ++ tailWord_1271171) baseStart_1271171 baseEnd_1271171 := by
    simpa [prefixWord, tailWord_1271171, baseEnd_1271171] using wordTrace_append hprefix tailTrace_1271171
  have hstable : (prefixWord ++ tailWord_1271171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271171).length < 2 ^ (prefixWord ++ tailWord_1271171).sum := by decide
  have hdescent : baseEnd_1271171 < baseStart_1271171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271175 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 1, 3, 2]
def baseStart_1271175 : Nat := 118140960795 + 1271175 * 2 ^ 59
def prefixEnd_1271175 : Nat := 4983230072969 + 3 ^ 40 * 1271175 * 2
def baseEnd_1271175 : Nat := 652723770979169255666479

theorem tailTrace_1271175 : CollatzResearch.WordTrace tailWord_1271175 prefixEnd_1271175 652723770979169255666479 := by
  unfold tailWord_1271175
  simp only [CollatzResearch.WordTrace]
  refine ⟨46363561169757549250942979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30909040779838366167295319 46363561169757549250942979)
  ·
    refine ⟨69545341754636323876414469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46363561169757549250942979 69545341754636323876414469)
    ·
      refine ⟨13039751578994310726827713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69545341754636323876414469 13039751578994310726827713)
      ·
        refine ⟨9779813684245733045120785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13039751578994310726827713 9779813684245733045120785)
        ·
          refine ⟨7334860263184299783840589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9779813684245733045120785 7334860263184299783840589)
          ·
            refine ⟨2750572598694112418940221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7334860263184299783840589 2750572598694112418940221)
            ·
              refine ⟨1031464724510292157102583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2750572598694112418940221 1031464724510292157102583)
              ·
                refine ⟨1547197086765438235653875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031464724510292157102583 1547197086765438235653875)
                ·
                  refine ⟨2320795630148157353480813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547197086765438235653875 2320795630148157353480813)
                  ·
                    refine ⟨870298361305559007555305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2320795630148157353480813 870298361305559007555305)
                    ·
                      refine ⟨652723770979169255666479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870298361305559007555305 652723770979169255666479)
                      ·
                        rfl

theorem cell23_1271175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_1271175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271175 prefixEnd_1271175 := by exact prefixLift 1271175
  have htrace : WordTrace (prefixWord ++ tailWord_1271175) baseStart_1271175 baseEnd_1271175 := by
    simpa [prefixWord, tailWord_1271175, baseEnd_1271175] using wordTrace_append hprefix tailTrace_1271175
  have hstable : (prefixWord ++ tailWord_1271175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271175).length < 2 ^ (prefixWord ++ tailWord_1271175).sum := by decide
  have hdescent : baseEnd_1271175 < baseStart_1271175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271194 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_1271194 : Nat := 118140960795 + 1271194 * 2 ^ 59
def prefixEnd_1271194 : Nat := 4983230072969 + 3 ^ 40 * 1271194 * 2
def baseEnd_1271194 : Nat := 72525947456844964592099

theorem tailTrace_1271194 : CollatzResearch.WordTrace tailWord_1271194 prefixEnd_1271194 72525947456844964592099 := by
  unfold tailWord_1271194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591063539172178873971159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30909502771125810330589757 11591063539172178873971159)
  ·
    refine ⟨17386595308758268310956739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11591063539172178873971159 17386595308758268310956739)
    ·
      refine ⟨26079892963137402466435109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17386595308758268310956739 26079892963137402466435109)
      ·
        refine ⟨4889979930588262962456583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26079892963137402466435109 4889979930588262962456583)
        ·
          refine ⟨7334969895882394443684875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889979930588262962456583 7334969895882394443684875)
          ·
            refine ⟨11002454843823591665527313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334969895882394443684875 11002454843823591665527313)
            ·
              refine ⟨8251841132867693749145485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11002454843823591665527313 8251841132867693749145485)
              ·
                refine ⟨3094440424825385155929557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8251841132867693749145485 3094440424825385155929557)
                ·
                  refine ⟨72525947456844964592099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3094440424825385155929557 72525947456844964592099)
                  ·
                    rfl

theorem cell23_1271194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_1271194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271194 prefixEnd_1271194 := by exact prefixLift 1271194
  have htrace : WordTrace (prefixWord ++ tailWord_1271194) baseStart_1271194 baseEnd_1271194 := by
    simpa [prefixWord, tailWord_1271194, baseEnd_1271194] using wordTrace_append hprefix tailTrace_1271194
  have hstable : (prefixWord ++ tailWord_1271194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271194).length < 2 ^ (prefixWord ++ tailWord_1271194).sum := by decide
  have hdescent : baseEnd_1271194 < baseStart_1271194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271198 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1271198 : Nat := 118140960795 + 1271198 * 2 ^ 59
def prefixEnd_1271198 : Nat := 4983230072969 + 3 ^ 40 * 1271198 * 2
def baseEnd_1271198 : Nat := 217578527011407555226291

theorem tailTrace_1271198 : CollatzResearch.WordTrace tailWord_1271198 prefixEnd_1271198 217578527011407555226291 := by
  unfold tailWord_1271198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795550006084278022378781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30909600032449482786020165 5795550006084278022378781)
  ·
    refine ⟨2173331252281604258392043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5795550006084278022378781 2173331252281604258392043)
    ·
      refine ⟨3259996878422406387588065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173331252281604258392043 3259996878422406387588065)
      ·
        refine ⟨2444997658816804790691049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3259996878422406387588065 2444997658816804790691049)
        ·
          refine ⟨1833748244112603593018287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2444997658816804790691049 1833748244112603593018287)
          ·
            refine ⟨2750622366168905389527431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833748244112603593018287 2750622366168905389527431)
            ·
              refine ⟨4125933549253358084291147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750622366168905389527431 4125933549253358084291147)
              ·
                refine ⟨6188900323880037126436721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125933549253358084291147 6188900323880037126436721)
                ·
                  refine ⟨4641675242910027844827541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6188900323880037126436721 4641675242910027844827541)
                  ·
                    refine ⟨217578527011407555226291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4641675242910027844827541 217578527011407555226291)
                    ·
                      rfl

theorem cell23_1271198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1271198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271198 prefixEnd_1271198 := by exact prefixLift 1271198
  have htrace : WordTrace (prefixWord ++ tailWord_1271198) baseStart_1271198 baseEnd_1271198 := by
    simpa [prefixWord, tailWord_1271198, baseEnd_1271198] using wordTrace_append hprefix tailTrace_1271198
  have hstable : (prefixWord ++ tailWord_1271198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271198).length < 2 ^ (prefixWord ++ tailWord_1271198).sum := by decide
  have hdescent : baseEnd_1271198 < baseStart_1271198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271261 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1271261 : Nat := 118140960795 + 1271261 * 2 ^ 59
def prefixEnd_1271261 : Nat := 4983230072969 + 3 ^ 40 * 1271261 * 2
def baseEnd_1271261 : Nat := 652767930315455919191083

theorem tailTrace_1271261 : CollatzResearch.WordTrace tailWord_1271261 prefixEnd_1271261 652767930315455919191083 := by
  unfold tailWord_1271261
  simp only [CollatzResearch.WordTrace]
  refine ⟨46366697847445985938573637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30911131898297323959049091 46366697847445985938573637)
  ·
    refine ⟨8693755846396122363482557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46366697847445985938573637 8693755846396122363482557)
    ·
      refine ⟨3260158442398545886305959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8693755846396122363482557 3260158442398545886305959)
      ·
        refine ⟨4890237663597818829458939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260158442398545886305959 4890237663597818829458939)
        ·
          refine ⟨7335356495396728244188409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890237663597818829458939 7335356495396728244188409)
          ·
            refine ⟨5501517371547546183141307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7335356495396728244188409 5501517371547546183141307)
            ·
              refine ⟨8252276057321319274711961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501517371547546183141307 8252276057321319274711961)
              ·
                refine ⟨6189207042990989456033971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8252276057321319274711961 6189207042990989456033971)
                ·
                  refine ⟨9283810564486484184050957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189207042990989456033971 9283810564486484184050957)
                  ·
                    refine ⟨3481428961682431569019109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9283810564486484184050957 3481428961682431569019109)
                    ·
                      refine ⟨652767930315455919191083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3481428961682431569019109 652767930315455919191083)
                      ·
                        rfl

theorem cell23_1271261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1271261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271261 prefixEnd_1271261 := by exact prefixLift 1271261
  have htrace : WordTrace (prefixWord ++ tailWord_1271261) baseStart_1271261 baseEnd_1271261 := by
    simpa [prefixWord, tailWord_1271261, baseEnd_1271261] using wordTrace_append hprefix tailTrace_1271261
  have hstable : (prefixWord ++ tailWord_1271261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271261).length < 2 ^ (prefixWord ++ tailWord_1271261).sum := by decide
  have hdescent : baseEnd_1271261 < baseStart_1271261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271281 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_1271281 : Nat := 118140960795 + 1271281 * 2 ^ 59
def prefixEnd_1271281 : Nat := 4983230072969 + 3 ^ 40 * 1271281 * 2
def baseEnd_1271281 : Nat := 652778199928545840940991

theorem tailTrace_1271281 : CollatzResearch.WordTrace tailWord_1271281 prefixEnd_1271281 652778199928545840940991 := by
  unfold tailWord_1271281
  simp only [CollatzResearch.WordTrace]
  refine ⟨46367427307373529354301697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30911618204915686236201131 46367427307373529354301697)
  ·
    refine ⟨34775570480530147015726273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46367427307373529354301697 34775570480530147015726273)
    ·
      refine ⟨26081677860397610261794705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34775570480530147015726273 26081677860397610261794705)
      ·
        refine ⟨19561258395298207696346029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26081677860397610261794705 19561258395298207696346029)
        ·
          refine ⟨7335471898236827886129761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19561258395298207696346029 7335471898236827886129761)
          ·
            refine ⟨5501603923677620914597321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7335471898236827886129761 5501603923677620914597321)
            ·
              refine ⟨4126202942758215685947991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5501603923677620914597321 4126202942758215685947991)
              ·
                refine ⟨6189304414137323528921987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126202942758215685947991 6189304414137323528921987)
                ·
                  refine ⟨9283956621205985293382981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189304414137323528921987 9283956621205985293382981)
                  ·
                    refine ⟨1740741866476122242509309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9283956621205985293382981 1740741866476122242509309)
                    ·
                      refine ⟨652778199928545840940991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740741866476122242509309 652778199928545840940991)
                      ·
                        rfl

theorem cell23_1271281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_1271281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271281 prefixEnd_1271281 := by exact prefixLift 1271281
  have htrace : WordTrace (prefixWord ++ tailWord_1271281) baseStart_1271281 baseEnd_1271281 := by
    simpa [prefixWord, tailWord_1271281, baseEnd_1271281] using wordTrace_append hprefix tailTrace_1271281
  have hstable : (prefixWord ++ tailWord_1271281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271281).length < 2 ^ (prefixWord ++ tailWord_1271281).sum := by decide
  have hdescent : baseEnd_1271281 < baseStart_1271281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271302 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1271302 : Nat := 118140960795 + 1271302 * 2 ^ 59
def prefixEnd_1271302 : Nat := 4983230072969 + 3 ^ 40 * 1271302 * 2
def baseEnd_1271302 : Nat := 652788983022290258778395

theorem tailTrace_1271302 : CollatzResearch.WordTrace tailWord_1271302 prefixEnd_1271302 652788983022290258778395 := by
  unfold tailWord_1271302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449006038759295310650505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30912128826864966627210773 1449006038759295310650505)
  ·
    refine ⟨1086754529069471482987879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1449006038759295310650505 1086754529069471482987879)
    ·
      refine ⟨1630131793604207224481819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086754529069471482987879 1630131793604207224481819)
      ·
        refine ⟨2445197690406310836722729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630131793604207224481819 2445197690406310836722729)
        ·
          refine ⟨1833898267804733127542047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2445197690406310836722729 1833898267804733127542047)
          ·
            refine ⟨2750847401707099691313071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833898267804733127542047 2750847401707099691313071)
            ·
              refine ⟨4126271102560649536969607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750847401707099691313071 4126271102560649536969607)
              ·
                refine ⟨6189406653840974305454411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126271102560649536969607 6189406653840974305454411)
                ·
                  refine ⟨9284109980761461458181617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189406653840974305454411 9284109980761461458181617)
                  ·
                    refine ⟨6963082485571096093636213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9284109980761461458181617 6963082485571096093636213)
                    ·
                      refine ⟨652788983022290258778395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6963082485571096093636213 652788983022290258778395)
                      ·
                        rfl

theorem cell23_1271302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1271302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271302 prefixEnd_1271302 := by exact prefixLift 1271302
  have htrace : WordTrace (prefixWord ++ tailWord_1271302) baseStart_1271302 baseEnd_1271302 := by
    simpa [prefixWord, tailWord_1271302, baseEnd_1271302] using wordTrace_append hprefix tailTrace_1271302
  have hstable : (prefixWord ++ tailWord_1271302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271302).length < 2 ^ (prefixWord ++ tailWord_1271302).sum := by decide
  have hdescent : baseEnd_1271302 < baseStart_1271302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271304 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_1271304 : Nat := 118140960795 + 1271304 * 2 ^ 59
def prefixEnd_1271304 : Nat := 4983230072969 + 3 ^ 40 * 1271304 * 2
def baseEnd_1271304 : Nat := 652790009983599250953385

theorem tailTrace_1271304 : CollatzResearch.WordTrace tailWord_1271304 prefixEnd_1271304 652790009983599250953385 := by
  unfold tailWord_1271304
  simp only [CollatzResearch.WordTrace]
  refine ⟨23184133093145102141194483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30912177457526802854925977 23184133093145102141194483)
  ·
    refine ⟨34776199639717653211791725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23184133093145102141194483 34776199639717653211791725)
    ·
      refine ⟨13041074864894119954421897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34776199639717653211791725 13041074864894119954421897)
      ·
        refine ⟨9780806148670589965816423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13041074864894119954421897 9780806148670589965816423)
        ·
          refine ⟨14671209223005884948724635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9780806148670589965816423 14671209223005884948724635)
          ·
            refine ⟨22006813834508827423086953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14671209223005884948724635 22006813834508827423086953)
            ·
              refine ⟨16505110375881620567315215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22006813834508827423086953 16505110375881620567315215)
              ·
                refine ⟨24757665563822430850972823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16505110375881620567315215 24757665563822430850972823)
                ·
                  refine ⟨37136498345733646276459235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24757665563822430850972823 37136498345733646276459235)
                  ·
                    refine ⟨55704747518600469414688853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37136498345733646276459235 55704747518600469414688853)
                    ·
                      refine ⟨652790009983599250953385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 55704747518600469414688853 652790009983599250953385)
                      ·
                        rfl

theorem cell23_1271304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_1271304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271304 prefixEnd_1271304 := by exact prefixLift 1271304
  have htrace : WordTrace (prefixWord ++ tailWord_1271304) baseStart_1271304 baseEnd_1271304 := by
    simpa [prefixWord, tailWord_1271304, baseEnd_1271304] using wordTrace_append hprefix tailTrace_1271304
  have hstable : (prefixWord ++ tailWord_1271304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271304).length < 2 ^ (prefixWord ++ tailWord_1271304).sum := by decide
  have hdescent : baseEnd_1271304 < baseStart_1271304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271305 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 1, 4]
def baseStart_1271305 : Nat := 118140960795 + 1271305 * 2 ^ 59
def prefixEnd_1271305 : Nat := 4983230072969 + 3 ^ 40 * 1271305 * 2
def baseEnd_1271305 : Nat := 217596841154751249013627

theorem tailTrace_1271305 : CollatzResearch.WordTrace tailWord_1271305 prefixEnd_1271305 217596841154751249013627 := by
  unfold tailWord_1271305
  simp only [CollatzResearch.WordTrace]
  refine ⟨46368302659286581453175369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30912201772857720968783579 46368302659286581453175369)
  ·
    refine ⟨34776226994464936089881527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46368302659286581453175369 34776226994464936089881527)
    ·
      refine ⟨52164340491697404134822291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34776226994464936089881527 52164340491697404134822291)
      ·
        refine ⟨78246510737546106202233437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52164340491697404134822291 78246510737546106202233437)
        ·
          refine ⟨29342441526579789825837539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78246510737546106202233437 29342441526579789825837539)
          ·
            refine ⟨44013662289869684738756309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29342441526579789825837539 44013662289869684738756309)
            ·
              refine ⟨1031570209918820736064601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44013662289869684738756309 1031570209918820736064601)
              ·
                refine ⟨773677657439115552048451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031570209918820736064601 773677657439115552048451)
                ·
                  refine ⟨1160516486158673328072677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773677657439115552048451 1160516486158673328072677)
                  ·
                    refine ⟨217596841154751249013627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160516486158673328072677 217596841154751249013627)
                    ·
                      rfl

theorem cell23_1271305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 4].length) (baseStart_1271305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271305 prefixEnd_1271305 := by exact prefixLift 1271305
  have htrace : WordTrace (prefixWord ++ tailWord_1271305) baseStart_1271305 baseEnd_1271305 := by
    simpa [prefixWord, tailWord_1271305, baseEnd_1271305] using wordTrace_append hprefix tailTrace_1271305
  have hstable : (prefixWord ++ tailWord_1271305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271305).length < 2 ^ (prefixWord ++ tailWord_1271305).sum := by decide
  have hdescent : baseEnd_1271305 < baseStart_1271305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271345 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 1, 1, 3]
def baseStart_1271345 : Nat := 118140960795 + 1271345 * 2 ^ 59
def prefixEnd_1271345 : Nat := 4983230072969 + 3 ^ 40 * 1271345 * 2
def baseEnd_1271345 : Nat := 652811062690433590540697

theorem tailTrace_1271345 : CollatzResearch.WordTrace tailWord_1271345 prefixEnd_1271345 652811062690433590540697 := by
  unfold tailWord_1271345
  simp only [CollatzResearch.WordTrace]
  refine ⟨46369761579141668284631489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30913174386094445523087659 46369761579141668284631489)
  ·
    refine ⟨34777321184356251213473617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46369761579141668284631489 34777321184356251213473617)
    ·
      refine ⟨26082990888267188410105213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34777321184356251213473617 26082990888267188410105213)
      ·
        refine ⟨9781121583100195653789455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26082990888267188410105213 9781121583100195653789455)
        ·
          refine ⟨14671682374650293480684183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9781121583100195653789455 14671682374650293480684183)
          ·
            refine ⟨22007523561975440221026275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14671682374650293480684183 22007523561975440221026275)
            ·
              refine ⟨33011285342963160331539413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22007523561975440221026275 33011285342963160331539413)
              ·
                refine ⟨773702000225699070270455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33011285342963160331539413 773702000225699070270455)
                ·
                  refine ⟨1160553000338548605405683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773702000225699070270455 1160553000338548605405683)
                  ·
                    refine ⟨1740829500507822908108525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160553000338548605405683 1740829500507822908108525)
                    ·
                      refine ⟨652811062690433590540697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1740829500507822908108525 652811062690433590540697)
                      ·
                        rfl

theorem cell23_1271345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_1271345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271345 prefixEnd_1271345 := by exact prefixLift 1271345
  have htrace : WordTrace (prefixWord ++ tailWord_1271345) baseStart_1271345 baseEnd_1271345 := by
    simpa [prefixWord, tailWord_1271345, baseEnd_1271345] using wordTrace_append hprefix tailTrace_1271345
  have hstable : (prefixWord ++ tailWord_1271345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271345).length < 2 ^ (prefixWord ++ tailWord_1271345).sum := by decide
  have hdescent : baseEnd_1271345 < baseStart_1271345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271361 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1271361 : Nat := 118140960795 + 1271361 * 2 ^ 59
def prefixEnd_1271361 : Nat := 4983230072969 + 3 ^ 40 * 1271361 * 2
def baseEnd_1271361 : Nat := 217606426126968509313541

theorem tailTrace_1271361 : CollatzResearch.WordTrace tailWord_1271361 prefixEnd_1271361 217606426126968509313541 := by
  unfold tailWord_1271361
  simp only [CollatzResearch.WordTrace]
  refine ⟨46370345147083703017213937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30913563431389135344809291 46370345147083703017213937)
  ·
    refine ⟨34777758860312777262910453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46370345147083703017213937 34777758860312777262910453)
    ·
      refine ⟨3260414893154322868397855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34777758860312777262910453 3260414893154322868397855)
      ·
        refine ⟨4890622339731484302596783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260414893154322868397855 4890622339731484302596783)
        ·
          refine ⟨7335933509597226453895175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890622339731484302596783 7335933509597226453895175)
          ·
            refine ⟨11003900264395839680842763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7335933509597226453895175 11003900264395839680842763)
            ·
              refine ⟨16505850396593759521264145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11003900264395839680842763 16505850396593759521264145)
              ·
                refine ⟨12379387797445319640948109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16505850396593759521264145 12379387797445319640948109)
                ·
                  refine ⟨4642270424041994865355541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12379387797445319640948109 4642270424041994865355541)
                  ·
                    refine ⟨217606426126968509313541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4642270424041994865355541 217606426126968509313541)
                    ·
                      rfl

theorem cell23_1271361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1271361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271361 prefixEnd_1271361 := by exact prefixLift 1271361
  have htrace : WordTrace (prefixWord ++ tailWord_1271361) baseStart_1271361 baseEnd_1271361 := by
    simpa [prefixWord, tailWord_1271361, baseEnd_1271361] using wordTrace_append hprefix tailTrace_1271361
  have hstable : (prefixWord ++ tailWord_1271361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271361).length < 2 ^ (prefixWord ++ tailWord_1271361).sum := by decide
  have hdescent : baseEnd_1271361 < baseStart_1271361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271378 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1271378 : Nat := 118140960795 + 1271378 * 2 ^ 59
def prefixEnd_1271378 : Nat := 4983230072969 + 3 ^ 40 * 1271378 * 2
def baseEnd_1271378 : Nat := 217609335850677320476015

theorem tailTrace_1271378 : CollatzResearch.WordTrace tailWord_1271378 prefixEnd_1271378 217609335850677320476015 := by
  unfold tailWord_1271378
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592741297005528730145697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30913976792014743280388525 11592741297005528730145697)
  ·
    refine ⟨8694555972754146547609273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11592741297005528730145697 8694555972754146547609273)
    ·
      refine ⟨6520916979565609910706955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8694555972754146547609273 6520916979565609910706955)
      ·
        refine ⟨9781375469348414866060433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6520916979565609910706955 9781375469348414866060433)
        ·
          refine ⟨7336031602011311149545325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9781375469348414866060433 7336031602011311149545325)
          ·
            refine ⟨2751011850754241681079497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7336031602011311149545325 2751011850754241681079497)
            ·
              refine ⟨2063258888065681260809623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751011850754241681079497 2063258888065681260809623)
              ·
                refine ⟨3094888332098521891214435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063258888065681260809623 3094888332098521891214435)
                ·
                  refine ⟨4642332498147782836821653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094888332098521891214435 4642332498147782836821653)
                  ·
                    refine ⟨217609335850677320476015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4642332498147782836821653 217609335850677320476015)
                    ·
                      rfl

theorem cell23_1271378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1271378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271378 prefixEnd_1271378 := by exact prefixLift 1271378
  have htrace : WordTrace (prefixWord ++ tailWord_1271378) baseStart_1271378 baseEnd_1271378 := by
    simpa [prefixWord, tailWord_1271378, baseEnd_1271378] using wordTrace_append hprefix tailTrace_1271378
  have hstable : (prefixWord ++ tailWord_1271378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271378).length < 2 ^ (prefixWord ++ tailWord_1271378).sum := by decide
  have hdescent : baseEnd_1271378 < baseStart_1271378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271402 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_1271402 : Nat := 118140960795 + 1271402 * 2 ^ 59
def prefixEnd_1271402 : Nat := 4983230072969 + 3 ^ 40 * 1271402 * 2
def baseEnd_1271402 : Nat := 652840331087739867527935

theorem tailTrace_1271402 : CollatzResearch.WordTrace tailWord_1271402 prefixEnd_1271402 652840331087739867527935 := by
  unfold tailWord_1271402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592960134983791754864115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30914560359956778012970973 11592960134983791754864115)
  ·
    refine ⟨17389440202475687632296173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11592960134983791754864115 17389440202475687632296173)
    ·
      refine ⟨6521040075928382862111065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17389440202475687632296173 6521040075928382862111065)
      ·
        refine ⟨4890780056946287146583299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6521040075928382862111065 4890780056946287146583299)
        ·
          refine ⟨7336170085419430719874949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890780056946287146583299 7336170085419430719874949)
          ·
            refine ⟨1375531891016143259976553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7336170085419430719874949 1375531891016143259976553)
            ·
              refine ⟨1031648918262107444982415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375531891016143259976553 1031648918262107444982415)
              ·
                refine ⟨1547473377393161167473623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031648918262107444982415 1547473377393161167473623)
                ·
                  refine ⟨2321210066089741751210435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547473377393161167473623 2321210066089741751210435)
                  ·
                    refine ⟨3481815099134612626815653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2321210066089741751210435 3481815099134612626815653)
                    ·
                      refine ⟨652840331087739867527935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3481815099134612626815653 652840331087739867527935)
                      ·
                        rfl

theorem cell23_1271402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_1271402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271402 prefixEnd_1271402 := by exact prefixLift 1271402
  have htrace : WordTrace (prefixWord ++ tailWord_1271402) baseStart_1271402 baseEnd_1271402 := by
    simpa [prefixWord, tailWord_1271402, baseEnd_1271402] using wordTrace_append hprefix tailTrace_1271402
  have hstable : (prefixWord ++ tailWord_1271402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271402).length < 2 ^ (prefixWord ++ tailWord_1271402).sum := by decide
  have hdescent : baseEnd_1271402 < baseStart_1271402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271432 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1271432 : Nat := 118140960795 + 1271432 * 2 ^ 59
def prefixEnd_1271432 : Nat := 4983230072969 + 3 ^ 40 * 1271432 * 2
def baseEnd_1271432 : Nat := 652855735507374750152797

theorem tailTrace_1271432 : CollatzResearch.WordTrace tailWord_1271432 prefixEnd_1271432 652855735507374750152797 := by
  unfold tailWord_1271432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23186467364913241071524275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30915289819884321428699033 23186467364913241071524275)
  ·
    refine ⟨34779701047369861607286413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23186467364913241071524275 34779701047369861607286413)
    ·
      refine ⟨13042387892763698102732405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34779701047369861607286413 13042387892763698102732405)
      ·
        refine ⟨1222723864946596697131163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13042387892763698102732405 1222723864946596697131163)
        ·
          refine ⟨1834085797419895045696745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222723864946596697131163 1834085797419895045696745)
          ·
            refine ⟨1375564348064921284272559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1834085797419895045696745 1375564348064921284272559)
            ·
              refine ⟨2063346522097381926408839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375564348064921284272559 2063346522097381926408839)
              ·
                refine ⟨3095019783146072889613259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063346522097381926408839 3095019783146072889613259)
                ·
                  refine ⟨4642529674719109334419889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095019783146072889613259 4642529674719109334419889)
                  ·
                    refine ⟨3481897256039332000814917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4642529674719109334419889 3481897256039332000814917)
                    ·
                      refine ⟨652855735507374750152797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3481897256039332000814917 652855735507374750152797)
                      ·
                        rfl

theorem cell23_1271432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1271432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271432 prefixEnd_1271432 := by exact prefixLift 1271432
  have htrace : WordTrace (prefixWord ++ tailWord_1271432) baseStart_1271432 baseEnd_1271432 := by
    simpa [prefixWord, tailWord_1271432, baseEnd_1271432] using wordTrace_append hprefix tailTrace_1271432
  have hstable : (prefixWord ++ tailWord_1271432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271432).length < 2 ^ (prefixWord ++ tailWord_1271432).sum := by decide
  have hdescent : baseEnd_1271432 < baseStart_1271432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271442 : List Nat := [3, 2, 3, 1, 4, 1, 2, 7]
def baseStart_1271442 : Nat := 118140960795 + 1271442 * 2 ^ 59
def prefixEnd_1271442 : Nat := 4983230072969 + 3 ^ 40 * 1271442 * 2
def baseEnd_1271442 : Nat := 24180032233848878186213

theorem tailTrace_1271442 : CollatzResearch.WordTrace tailWord_1271442 prefixEnd_1271442 24180032233848878186213 := by
  unfold tailWord_1271442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593324864947563462728145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30915532973193502567275053 11593324864947563462728145)
  ·
    refine ⟨8694993648710672597046109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11593324864947563462728145 8694993648710672597046109)
    ·
      refine ⟨3260622618266502223892291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8694993648710672597046109 3260622618266502223892291)
      ·
        refine ⟨4890933927399753335838437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260622618266502223892291 4890933927399753335838437)
        ·
          refine ⟨917050111387453750469707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4890933927399753335838437 917050111387453750469707)
          ·
            refine ⟨1375575167081180625704561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917050111387453750469707 1375575167081180625704561)
            ·
              refine ⟨1031681375310885469278421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375575167081180625704561 1031681375310885469278421)
              ·
                refine ⟨24180032233848878186213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1031681375310885469278421 24180032233848878186213)
                ·
                  rfl

theorem cell23_1271442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_1271442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271442 prefixEnd_1271442 := by exact prefixLift 1271442
  have htrace : WordTrace (prefixWord ++ tailWord_1271442) baseStart_1271442 baseEnd_1271442 := by
    simpa [prefixWord, tailWord_1271442, baseEnd_1271442] using wordTrace_append hprefix tailTrace_1271442
  have hstable : (prefixWord ++ tailWord_1271442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271442).length < 2 ^ (prefixWord ++ tailWord_1271442).sum := by decide
  have hdescent : baseEnd_1271442 < baseStart_1271442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271461 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_1271461 : Nat := 118140960795 + 1271461 * 2 ^ 59
def prefixEnd_1271461 : Nat := 4983230072969 + 3 ^ 40 * 1271461 * 2
def baseEnd_1271461 : Nat := 652870626446355136690163

theorem tailTrace_1271461 : CollatzResearch.WordTrace tailWord_1271461 prefixEnd_1271461 652870626446355136690163 := by
  unfold tailWord_1271461
  simp only [CollatzResearch.WordTrace]
  refine ⟨46373992446721420095854237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30915994964480946730569491 46373992446721420095854237)
  ·
    refine ⟨17390247167520532535945339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46373992446721420095854237 17390247167520532535945339)
    ·
      refine ⟨26085370751280798803918009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17390247167520532535945339 26085370751280798803918009)
      ·
        refine ⟨19564028063460599102938507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26085370751280798803918009 19564028063460599102938507)
        ·
          refine ⟨29346042095190898654407761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19564028063460599102938507 29346042095190898654407761)
          ·
            refine ⟨22009531571393173990805821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29346042095190898654407761 22009531571393173990805821)
            ·
              refine ⟨8253574339272440246552183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22009531571393173990805821 8253574339272440246552183)
              ·
                refine ⟨12380361508908660369828275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253574339272440246552183 12380361508908660369828275)
                ·
                  refine ⟨18570542263362990554742413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12380361508908660369828275 18570542263362990554742413)
                  ·
                    refine ⟨6963953348761121458028405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18570542263362990554742413 6963953348761121458028405)
                    ·
                      refine ⟨652870626446355136690163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6963953348761121458028405 652870626446355136690163)
                      ·
                        rfl

theorem cell23_1271461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_1271461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271461 prefixEnd_1271461 := by exact prefixLift 1271461
  have htrace : WordTrace (prefixWord ++ tailWord_1271461) baseStart_1271461 baseEnd_1271461 := by
    simpa [prefixWord, tailWord_1271461, baseEnd_1271461] using wordTrace_append hprefix tailTrace_1271461
  have hstable : (prefixWord ++ tailWord_1271461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271461).length < 2 ^ (prefixWord ++ tailWord_1271461).sum := by decide
  have hdescent : baseEnd_1271461 < baseStart_1271461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271475 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 4, 2, 2]
def baseStart_1271475 : Nat := 118140960795 + 1271475 * 2 ^ 59
def prefixEnd_1271475 : Nat := 4983230072969 + 3 ^ 40 * 1271475 * 2
def baseEnd_1271475 : Nat := 652877815175518081915099

theorem tailTrace_1271475 : CollatzResearch.WordTrace tailWord_1271475 prefixEnd_1271475 652877815175518081915099 := by
  unfold tailWord_1271475
  simp only [CollatzResearch.WordTrace]
  refine ⟨46374503068670700486863879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30916335379113800324575919 46374503068670700486863879)
  ·
    refine ⟨69561754603006050730295819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46374503068670700486863879 69561754603006050730295819)
    ·
      refine ⟨104342631904509076095443729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69561754603006050730295819 104342631904509076095443729)
      ·
        refine ⟨78256973928381807071582797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104342631904509076095443729 78256973928381807071582797)
        ·
          refine ⟨29346365223143177651843549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78256973928381807071582797 29346365223143177651843549)
          ·
            refine ⟨11004886958678691619441331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29346365223143177651843549 11004886958678691619441331)
            ·
              refine ⟨16507330438018037429161997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11004886958678691619441331 16507330438018037429161997)
              ·
                refine ⟨6190248914256764035935749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16507330438018037429161997 6190248914256764035935749)
                ·
                  refine ⟨1160671671423143256737953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6190248914256764035935749 1160671671423143256737953)
                  ·
                    refine ⟨870503753567357442553465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1160671671423143256737953 870503753567357442553465)
                    ·
                      refine ⟨652877815175518081915099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870503753567357442553465 652877815175518081915099)
                      ·
                        rfl

theorem cell23_1271475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 2, 2].length) (baseStart_1271475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271475 prefixEnd_1271475 := by exact prefixLift 1271475
  have htrace : WordTrace (prefixWord ++ tailWord_1271475) baseStart_1271475 baseEnd_1271475 := by
    simpa [prefixWord, tailWord_1271475, baseEnd_1271475] using wordTrace_append hprefix tailTrace_1271475
  have hstable : (prefixWord ++ tailWord_1271475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271475).length < 2 ^ (prefixWord ++ tailWord_1271475).sum := by decide
  have hdescent : baseEnd_1271475 < baseStart_1271475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271538 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1271538 : Nat := 118140960795 + 1271538 * 2 ^ 59
def prefixEnd_1271538 : Nat := 4983230072969 + 3 ^ 40 * 1271538 * 2
def baseEnd_1271538 : Nat := 652910164456751335427309

theorem tailTrace_1271538 : CollatzResearch.WordTrace tailWord_1271538 prefixEnd_1271538 652910164456751335427309 := by
  unfold tailWord_1271538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594200216860615561601817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30917867244961641497604845 11594200216860615561601817)
  ·
    refine ⟨8695650162645461671201363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11594200216860615561601817 8695650162645461671201363)
    ·
      refine ⟨13043475243968192506802045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8695650162645461671201363 13043475243968192506802045)
      ·
        refine ⟨4891303216488072190050767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13043475243968192506802045 4891303216488072190050767)
        ·
          refine ⟨7336954824732108285076151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891303216488072190050767 7336954824732108285076151)
          ·
            refine ⟨11005432237098162427614227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336954824732108285076151 11005432237098162427614227)
            ·
              refine ⟨16508148355647243641421341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11005432237098162427614227 16508148355647243641421341)
              ·
                refine ⟨6190555633367716365533003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16508148355647243641421341 6190555633367716365533003)
                ·
                  refine ⟨9285833450051574548299505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190555633367716365533003 9285833450051574548299505)
                  ·
                    refine ⟨6964375087538680911224629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9285833450051574548299505 6964375087538680911224629)
                    ·
                      refine ⟨652910164456751335427309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6964375087538680911224629 652910164456751335427309)
                      ·
                        rfl

theorem cell23_1271538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1271538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271538 prefixEnd_1271538 := by exact prefixLift 1271538
  have htrace : WordTrace (prefixWord ++ tailWord_1271538) baseStart_1271538 baseEnd_1271538 := by
    simpa [prefixWord, tailWord_1271538, baseEnd_1271538] using wordTrace_append hprefix tailTrace_1271538
  have hstable : (prefixWord ++ tailWord_1271538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271538).length < 2 ^ (prefixWord ++ tailWord_1271538).sum := by decide
  have hdescent : baseEnd_1271538 < baseStart_1271538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271548 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1271548 : Nat := 118140960795 + 1271548 * 2 ^ 59
def prefixEnd_1271548 : Nat := 4983230072969 + 3 ^ 40 * 1271548 * 2
def baseEnd_1271548 : Nat := 652915299263296296302263

theorem tailTrace_1271548 : CollatzResearch.WordTrace tailWord_1271548 prefixEnd_1271548 652915299263296296302263 := by
  unfold tailWord_1271548
  simp only [CollatzResearch.WordTrace]
  refine ⟨23188582798703116977135649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30918110398270822636180865 23188582798703116977135649)
  ·
    refine ⟨17391437099027337732851737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23188582798703116977135649 17391437099027337732851737)
    ·
      refine ⟨13043577824270503299638803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17391437099027337732851737 13043577824270503299638803)
      ·
        refine ⟨19565366736405754949458205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13043577824270503299638803 19565366736405754949458205)
        ·
          refine ⟨7337012526152158106046827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19565366736405754949458205 7337012526152158106046827)
          ·
            refine ⟨11005518789228237159070241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337012526152158106046827 11005518789228237159070241)
            ·
              refine ⟨8254139091921177869302681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11005518789228237159070241 8254139091921177869302681)
              ·
                refine ⟨6190604318940883401977011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8254139091921177869302681 6190604318940883401977011)
                ·
                  refine ⟨9285906478411325102965517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190604318940883401977011 9285906478411325102965517)
                  ·
                    refine ⟨3482214929404246913612069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9285906478411325102965517 3482214929404246913612069)
                    ·
                      refine ⟨652915299263296296302263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3482214929404246913612069 652915299263296296302263)
                      ·
                        rfl

theorem cell23_1271548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1271548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271548 prefixEnd_1271548 := by exact prefixLift 1271548
  have htrace : WordTrace (prefixWord ++ tailWord_1271548) baseStart_1271548 baseEnd_1271548 := by
    simpa [prefixWord, tailWord_1271548, baseEnd_1271548] using wordTrace_append hprefix tailTrace_1271548
  have hstable : (prefixWord ++ tailWord_1271548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271548).length < 2 ^ (prefixWord ++ tailWord_1271548).sum := by decide
  have hdescent : baseEnd_1271548 < baseStart_1271548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271578 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1271578 : Nat := 118140960795 + 1271578 * 2 ^ 59
def prefixEnd_1271578 : Nat := 4983230072969 + 3 ^ 40 * 1271578 * 2
def baseEnd_1271578 : Nat := 652930703682931178927125

theorem tailTrace_1271578 : CollatzResearch.WordTrace tailWord_1271578 prefixEnd_1271578 652930703682931178927125 := by
  unfold tailWord_1271578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594564946824387269465847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30918839858198366051908925 11594564946824387269465847)
  ·
    refine ⟨17391847420236580904198771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11594564946824387269465847 17391847420236580904198771)
    ·
      refine ⟨26087771130354871356298157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17391847420236580904198771 26087771130354871356298157)
      ·
        refine ⟨9782914173883076758611809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26087771130354871356298157 9782914173883076758611809)
        ·
          refine ⟨7337185630412307568958857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782914173883076758611809 7337185630412307568958857)
          ·
            refine ⟨5502889222809230676719143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7337185630412307568958857 5502889222809230676719143)
            ·
              refine ⟨8254333834213846015078715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502889222809230676719143 8254333834213846015078715)
              ·
                refine ⟨12381500751320769022618073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8254333834213846015078715 12381500751320769022618073)
                ·
                  refine ⟨9286125563490576766963555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12381500751320769022618073 9286125563490576766963555)
                  ·
                    refine ⟨13929188345235865150445333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9286125563490576766963555 13929188345235865150445333)
                    ·
                      refine ⟨652930703682931178927125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13929188345235865150445333 652930703682931178927125)
                      ·
                        rfl

theorem cell23_1271578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1271578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271578 prefixEnd_1271578 := by exact prefixLift 1271578
  have htrace : WordTrace (prefixWord ++ tailWord_1271578) baseStart_1271578 baseEnd_1271578 := by
    simpa [prefixWord, tailWord_1271578, baseEnd_1271578] using wordTrace_append hprefix tailTrace_1271578
  have hstable : (prefixWord ++ tailWord_1271578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271578).length < 2 ^ (prefixWord ++ tailWord_1271578).sum := by decide
  have hdescent : baseEnd_1271578 < baseStart_1271578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271592 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1271592 : Nat := 118140960795 + 1271592 * 2 ^ 59
def prefixEnd_1271592 : Nat := 4983230072969 + 3 ^ 40 * 1271592 * 2
def baseEnd_1271592 : Nat := 217645964137364708050687

theorem tailTrace_1271592 : CollatzResearch.WordTrace tailWord_1271592 prefixEnd_1271592 217645964137364708050687 := by
  unfold tailWord_1271592
  simp only [CollatzResearch.WordTrace]
  refine ⟨23189385204623414734436515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30919180272831219645915353 23189385204623414734436515)
  ·
    refine ⟨34784077806935122101654773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23189385204623414734436515 34784077806935122101654773)
    ·
      refine ⟨3261007294400167697030135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34784077806935122101654773 3261007294400167697030135)
      ·
        refine ⟨4891510941600251545545203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3261007294400167697030135 4891510941600251545545203)
        ·
          refine ⟨7337266412400377318317805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891510941600251545545203 7337266412400377318317805)
          ·
            refine ⟨2751474904650141494369177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7337266412400377318317805 2751474904650141494369177)
            ·
              refine ⟨2063606178487606120776883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751474904650141494369177 2063606178487606120776883)
              ·
                refine ⟨3095409267731409181165325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063606178487606120776883 3095409267731409181165325)
                ·
                  refine ⟨1160778475399278442936997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3095409267731409181165325 1160778475399278442936997)
                  ·
                    refine ⟨217645964137364708050687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1160778475399278442936997 217645964137364708050687)
                    ·
                      rfl

theorem cell23_1271592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1271592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271592 prefixEnd_1271592 := by exact prefixLift 1271592
  have htrace : WordTrace (prefixWord ++ tailWord_1271592) baseStart_1271592 baseEnd_1271592 := by
    simpa [prefixWord, tailWord_1271592, baseEnd_1271592] using wordTrace_append hprefix tailTrace_1271592
  have hstable : (prefixWord ++ tailWord_1271592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271592).length < 2 ^ (prefixWord ++ tailWord_1271592).sum := by decide
  have hdescent : baseEnd_1271592 < baseStart_1271592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271622 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1271622 : Nat := 118140960795 + 1271622 * 2 ^ 59
def prefixEnd_1271622 : Nat := 4983230072969 + 3 ^ 40 * 1271622 * 2
def baseEnd_1271622 : Nat := 72550366314636556308547

theorem tailTrace_1271622 : CollatzResearch.WordTrace tailWord_1271622 prefixEnd_1271622 72550366314636556308547 := by
  unfold tailWord_1271622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449370768723067018514535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30919909732758763061643413 1449370768723067018514535)
  ·
    refine ⟨2174056153084600527771803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449370768723067018514535 2174056153084600527771803)
    ·
      refine ⟨3261084229626900791657705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174056153084600527771803 3261084229626900791657705)
      ·
        refine ⟨2445813172220175593743279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3261084229626900791657705 2445813172220175593743279)
        ·
          refine ⟨3668719758330263390614919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2445813172220175593743279 3668719758330263390614919)
          ·
            refine ⟨5503079637495395085922379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668719758330263390614919 5503079637495395085922379)
            ·
              refine ⟨8254619456243092628883569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5503079637495395085922379 8254619456243092628883569)
              ·
                refine ⟨6190964592182319471662677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8254619456243092628883569 6190964592182319471662677)
                ·
                  refine ⟨72550366314636556308547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6190964592182319471662677 72550366314636556308547)
                  ·
                    rfl

theorem cell23_1271622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1271622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271622 prefixEnd_1271622 := by exact prefixLift 1271622
  have htrace : WordTrace (prefixWord ++ tailWord_1271622) baseStart_1271622 baseEnd_1271622 := by
    simpa [prefixWord, tailWord_1271622, baseEnd_1271622] using wordTrace_append hprefix tailTrace_1271622
  have hstable : (prefixWord ++ tailWord_1271622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271622).length < 2 ^ (prefixWord ++ tailWord_1271622).sum := by decide
  have hdescent : baseEnd_1271622 < baseStart_1271622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271625 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 1, 5, 2]
def baseStart_1271625 : Nat := 118140960795 + 1271625 * 2 ^ 59
def prefixEnd_1271625 : Nat := 4983230072969 + 3 ^ 40 * 1271625 * 2
def baseEnd_1271625 : Nat := 652954837273692495039409

theorem tailTrace_1271625 : CollatzResearch.WordTrace tailWord_1271625 prefixEnd_1271625 652954837273692495039409 := by
  unfold tailWord_1271625
  simp only [CollatzResearch.WordTrace]
  refine ⟨46379974018127276104824329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30919982678751517403216219 46379974018127276104824329)
  ·
    refine ⟨34784980513595457078618247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46379974018127276104824329 34784980513595457078618247)
    ·
      refine ⟨52177470770393185617927371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34784980513595457078618247 52177470770393185617927371)
      ·
        refine ⟨78266206155589778426891057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52177470770393185617927371 78266206155589778426891057)
        ·
          refine ⟨58699654616692333820168293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78266206155589778426891057 58699654616692333820168293)
          ·
            refine ⟨11006185240629812591281555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58699654616692333820168293 11006185240629812591281555)
            ·
              refine ⟨16509277860944718886922333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11006185240629812591281555 16509277860944718886922333)
              ·
                refine ⟨6190979197854269582595875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16509277860944718886922333 6190979197854269582595875)
                ·
                  refine ⟨9286468796781404373893813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190979197854269582595875 9286468796781404373893813)
                  ·
                    refine ⟨870606449698256660052545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9286468796781404373893813 870606449698256660052545)
                    ·
                      refine ⟨652954837273692495039409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870606449698256660052545 652954837273692495039409)
                      ·
                        rfl

theorem cell23_1271625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 5, 2].length) (baseStart_1271625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271625 prefixEnd_1271625 := by exact prefixLift 1271625
  have htrace : WordTrace (prefixWord ++ tailWord_1271625) baseStart_1271625 baseEnd_1271625 := by
    simpa [prefixWord, tailWord_1271625, baseEnd_1271625] using wordTrace_append hprefix tailTrace_1271625
  have hstable : (prefixWord ++ tailWord_1271625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271625).length < 2 ^ (prefixWord ++ tailWord_1271625).sum := by decide
  have hdescent : baseEnd_1271625 < baseStart_1271625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271642 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2]
def baseStart_1271642 : Nat := 118140960795 + 1271642 * 2 ^ 59
def prefixEnd_1271642 : Nat := 4983230072969 + 3 ^ 40 * 1271642 * 2
def baseEnd_1271642 : Nat := 652963566444818928526831

theorem tailTrace_1271642 : CollatzResearch.WordTrace tailWord_1271642 prefixEnd_1271642 652963566444818928526831 := by
  unfold tailWord_1271642
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595148514766422002048295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30920396039377125338795453 11595148514766422002048295)
  ·
    refine ⟨17392722772149633003072443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11595148514766422002048295 17392722772149633003072443)
    ·
      refine ⟨26089084158224449504608665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17392722772149633003072443 26089084158224449504608665)
      ·
        refine ⟨19566813118668337128456499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26089084158224449504608665 19566813118668337128456499)
        ·
          refine ⟨29350219678002505692684749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19566813118668337128456499 29350219678002505692684749)
          ·
            refine ⟨11006332379250939634756781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29350219678002505692684749 11006332379250939634756781)
            ·
              refine ⟨4127374642219102363033793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11006332379250939634756781 4127374642219102363033793)
              ·
                refine ⟨3095530981664326772275345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127374642219102363033793 3095530981664326772275345)
                ·
                  refine ⟨2321648236248245079206509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095530981664326772275345 2321648236248245079206509)
                  ·
                    refine ⟨870618088593091904702441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2321648236248245079206509 870618088593091904702441)
                    ·
                      refine ⟨652963566444818928526831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870618088593091904702441 652963566444818928526831)
                      ·
                        rfl

theorem cell23_1271642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_1271642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271642 prefixEnd_1271642 := by exact prefixLift 1271642
  have htrace : WordTrace (prefixWord ++ tailWord_1271642) baseStart_1271642 baseEnd_1271642 := by
    simpa [prefixWord, tailWord_1271642, baseEnd_1271642] using wordTrace_append hprefix tailTrace_1271642
  have hstable : (prefixWord ++ tailWord_1271642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271642).length < 2 ^ (prefixWord ++ tailWord_1271642).sum := by decide
  have hdescent : baseEnd_1271642 < baseStart_1271642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271655 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1271655 : Nat := 118140960795 + 1271655 * 2 ^ 59
def prefixEnd_1271655 : Nat := 4983230072969 + 3 ^ 40 * 1271655 * 2
def baseEnd_1271655 : Nat := 652970241693327377664271

theorem tailTrace_1271655 : CollatzResearch.WordTrace tailWord_1271655 prefixEnd_1271655 652970241693327377664271 := by
  unfold tailWord_1271655
  simp only [CollatzResearch.WordTrace]
  refine ⟨46381068208018591228416419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30920712138679060818944279 46381068208018591228416419)
  ·
    refine ⟨69571602312027886842624629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46381068208018591228416419 69571602312027886842624629)
    ·
      refine ⟨6522337716752614391496059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69571602312027886842624629 6522337716752614391496059)
      ·
        refine ⟨9783506575128921587244089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6522337716752614391496059 9783506575128921587244089)
        ·
          refine ⟨7337629931346691190433067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9783506575128921587244089 7337629931346691190433067)
          ·
            refine ⟨11006444897020036785649601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337629931346691190433067 11006444897020036785649601)
            ·
              refine ⟨8254833672765027589237201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11006444897020036785649601 8254833672765027589237201)
              ·
                refine ⟨6191125254573770691927901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8254833672765027589237201 6191125254573770691927901)
                ·
                  refine ⟨2321671970465164009472963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6191125254573770691927901 2321671970465164009472963)
                  ·
                    refine ⟨3482507955697746014209445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2321671970465164009472963 3482507955697746014209445)
                    ·
                      refine ⟨652970241693327377664271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3482507955697746014209445 652970241693327377664271)
                      ·
                        rfl

theorem cell23_1271655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1271655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271655 prefixEnd_1271655 := by exact prefixLift 1271655
  have htrace : WordTrace (prefixWord ++ tailWord_1271655) baseStart_1271655 baseEnd_1271655 := by
    simpa [prefixWord, tailWord_1271655, baseEnd_1271655] using wordTrace_append hprefix tailTrace_1271655
  have hstable : (prefixWord ++ tailWord_1271655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271655).length < 2 ^ (prefixWord ++ tailWord_1271655).sum := by decide
  have hdescent : baseEnd_1271655 < baseStart_1271655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271685 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_1271685 : Nat := 118140960795 + 1271685 * 2 ^ 59
def prefixEnd_1271685 : Nat := 4983230072969 + 3 ^ 40 * 1271685 * 2
def baseEnd_1271685 : Nat := 652985646112962260289133

theorem tailTrace_1271685 : CollatzResearch.WordTrace tailWord_1271685 prefixEnd_1271685 652985646112962260289133 := by
  unfold tailWord_1271685
  simp only [CollatzResearch.WordTrace]
  refine ⟨46382162397909906352008509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30921441598606604234672339 46382162397909906352008509)
  ·
    refine ⟨17393310899216214882003191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46382162397909906352008509 17393310899216214882003191)
    ·
      refine ⟨26089966348824322323004787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17393310899216214882003191 26089966348824322323004787)
      ·
        refine ⟨39134949523236483484507181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26089966348824322323004787 39134949523236483484507181)
        ·
          refine ⟨14675606071213681306690193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39134949523236483484507181 14675606071213681306690193)
          ·
            refine ⟨11006704553410260980017645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14675606071213681306690193 11006704553410260980017645)
            ·
              refine ⟨4127514207528847867506617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11006704553410260980017645 4127514207528847867506617)
              ·
                refine ⟨3095635655646635900629963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127514207528847867506617 3095635655646635900629963)
                ·
                  refine ⟨4643453483469953850944945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095635655646635900629963 4643453483469953850944945)
                  ·
                    refine ⟨3482590112602465388208709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643453483469953850944945 3482590112602465388208709)
                    ·
                      refine ⟨652985646112962260289133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3482590112602465388208709 652985646112962260289133)
                      ·
                        rfl

theorem cell23_1271685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_1271685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271685 prefixEnd_1271685 := by exact prefixLift 1271685
  have htrace : WordTrace (prefixWord ++ tailWord_1271685) baseStart_1271685 baseEnd_1271685 := by
    simpa [prefixWord, tailWord_1271685, baseEnd_1271685] using wordTrace_append hprefix tailTrace_1271685
  have hstable : (prefixWord ++ tailWord_1271685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271685).length < 2 ^ (prefixWord ++ tailWord_1271685).sum := by decide
  have hdescent : baseEnd_1271685 < baseStart_1271685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271740 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1271740 : Nat := 118140960795 + 1271740 * 2 ^ 59
def prefixEnd_1271740 : Nat := 4983230072969 + 3 ^ 40 * 1271740 * 2
def baseEnd_1271740 : Nat := 653013887548959545101381

theorem tailTrace_1271740 : CollatzResearch.WordTrace tailWord_1271740 prefixEnd_1271740 653013887548959545101381 := by
  unfold tailWord_1271740
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192084206355325372630337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30922778941807100496840449 23192084206355325372630337)
  ·
    refine ⟨17394063154766494029472753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23192084206355325372630337 17394063154766494029472753)
    ·
      refine ⟨13045547366074870522104565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17394063154766494029472753 13045547366074870522104565)
      ·
        refine ⟨1223020065569519111447303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13045547366074870522104565 1223020065569519111447303)
        ·
          refine ⟨1834530098354278667170955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223020065569519111447303 1834530098354278667170955)
          ·
            refine ⟨2751795147531418000756433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834530098354278667170955 2751795147531418000756433)
            ·
              refine ⟨2063846360648563500567325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751795147531418000756433 2063846360648563500567325)
              ·
                refine ⟨773942385243211312712747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063846360648563500567325 773942385243211312712747)
                ·
                  refine ⟨1160913577864816969069121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773942385243211312712747 1160913577864816969069121)
                  ·
                    refine ⟨870685183398612726801841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1160913577864816969069121 870685183398612726801841)
                    ·
                      refine ⟨653013887548959545101381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870685183398612726801841 653013887548959545101381)
                      ·
                        rfl

theorem cell23_1271740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1271740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271740 prefixEnd_1271740 := by exact prefixLift 1271740
  have htrace : WordTrace (prefixWord ++ tailWord_1271740) baseStart_1271740 baseEnd_1271740 := by
    simpa [prefixWord, tailWord_1271740, baseEnd_1271740] using wordTrace_append hprefix tailTrace_1271740
  have hstable : (prefixWord ++ tailWord_1271740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271740).length < 2 ^ (prefixWord ++ tailWord_1271740).sum := by decide
  have hdescent : baseEnd_1271740 < baseStart_1271740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271756 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1271756 : Nat := 118140960795 + 1271756 * 2 ^ 59
def prefixEnd_1271756 : Nat := 4983230072969 + 3 ^ 40 * 1271756 * 2
def baseEnd_1271756 : Nat := 653022103239431482501307

theorem tailTrace_1271756 : CollatzResearch.WordTrace tailWord_1271756 prefixEnd_1271756 653022103239431482501307 := by
  unfold tailWord_1271756
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192375990326342738921561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30923167987101790318562081 23192375990326342738921561)
  ·
    refine ⟨17394281992744757054191171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23192375990326342738921561 17394281992744757054191171)
    ·
      refine ⟨26091422989117135581286757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17394281992744757054191171 26091422989117135581286757)
      ·
        refine ⟨4892141810459462921491267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26091422989117135581286757 4892141810459462921491267)
        ·
          refine ⟨7338212715689194382236901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4892141810459462921491267 7338212715689194382236901)
          ·
            refine ⟨1375914884191723946669419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7338212715689194382236901 1375914884191723946669419)
            ·
              refine ⟨2063872326287585920004129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375914884191723946669419 2063872326287585920004129)
              ·
                refine ⟨1547904244715689440003097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063872326287585920004129 1547904244715689440003097)
                ·
                  refine ⟨1160928183536767080002323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1547904244715689440003097 1160928183536767080002323)
                  ·
                    refine ⟨1741392275305150620003485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160928183536767080002323 1741392275305150620003485)
                    ·
                      refine ⟨653022103239431482501307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741392275305150620003485 653022103239431482501307)
                      ·
                        rfl

theorem cell23_1271756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1271756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271756 prefixEnd_1271756 := by exact prefixLift 1271756
  have htrace : WordTrace (prefixWord ++ tailWord_1271756) baseStart_1271756 baseEnd_1271756 := by
    simpa [prefixWord, tailWord_1271756, baseEnd_1271756] using wordTrace_append hprefix tailTrace_1271756
  have hstable : (prefixWord ++ tailWord_1271756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271756).length < 2 ^ (prefixWord ++ tailWord_1271756).sum := by decide
  have hdescent : baseEnd_1271756 < baseStart_1271756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271773 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_1271773 : Nat := 118140960795 + 1271773 * 2 ^ 59
def prefixEnd_1271773 : Nat := 4983230072969 + 3 ^ 40 * 1271773 * 2
def baseEnd_1271773 : Nat := 653030832410557915988729

theorem tailTrace_1271773 : CollatzResearch.WordTrace tailWord_1271773 prefixEnd_1271773 653030832410557915988729 := by
  unfold tailWord_1271773
  simp only [CollatzResearch.WordTrace]
  refine ⟨46385372021591097381211973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30923581347727398254141315 46385372021591097381211973)
  ·
    refine ⟨8697257254048330758977245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46385372021591097381211973 8697257254048330758977245)
    ·
      refine ⟨3261471470268124034616467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8697257254048330758977245 3261471470268124034616467)
      ·
        refine ⟨4892207205402186051924701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3261471470268124034616467 4892207205402186051924701)
        ·
          refine ⟨1834577702025819769471763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4892207205402186051924701 1834577702025819769471763)
          ·
            refine ⟨2751866553038729654207645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834577702025819769471763 2751866553038729654207645)
            ·
              refine ⟨1031949957389523620327867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2751866553038729654207645 1031949957389523620327867)
              ·
                refine ⟨1547924936084285430491801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031949957389523620327867 1547924936084285430491801)
                ·
                  refine ⟨1160943702063214072868851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1547924936084285430491801 1160943702063214072868851)
                  ·
                    refine ⟨1741415553094821109303277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160943702063214072868851 1741415553094821109303277)
                    ·
                      refine ⟨653030832410557915988729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741415553094821109303277 653030832410557915988729)
                      ·
                        rfl

theorem cell23_1271773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_1271773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271773 prefixEnd_1271773 := by exact prefixLift 1271773
  have htrace : WordTrace (prefixWord ++ tailWord_1271773) baseStart_1271773 baseEnd_1271773 := by
    simpa [prefixWord, tailWord_1271773, baseEnd_1271773] using wordTrace_append hprefix tailTrace_1271773
  have hstable : (prefixWord ++ tailWord_1271773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271773).length < 2 ^ (prefixWord ++ tailWord_1271773).sum := by decide
  have hdescent : baseEnd_1271773 < baseStart_1271773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271779 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 1, 4, 2]
def baseStart_1271779 : Nat := 118140960795 + 1271779 * 2 ^ 59
def prefixEnd_1271779 : Nat := 4983230072969 + 3 ^ 40 * 1271779 * 2
def baseEnd_1271779 : Nat := 653033913294484892513701

theorem tailTrace_1271779 : CollatzResearch.WordTrace tailWord_1271779 prefixEnd_1271779 653033913294484892513701 := by
  unfold tailWord_1271779
  simp only [CollatzResearch.WordTrace]
  refine ⟨46385590859569360405930391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30923727239712906937286927 46385590859569360405930391)
  ·
    refine ⟨69578386289354040608895587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46385590859569360405930391 69578386289354040608895587)
    ·
      refine ⟨104367579434031060913343381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69578386289354040608895587 104367579434031060913343381)
      ·
        refine ⟨4892230285970205980312971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104367579434031060913343381 4892230285970205980312971)
        ·
          refine ⟨7338345428955308970469457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4892230285970205980312971 7338345428955308970469457)
          ·
            refine ⟨5503759071716481727852093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7338345428955308970469457 5503759071716481727852093)
            ·
              refine ⟨2063909651893680647944535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5503759071716481727852093 2063909651893680647944535)
              ·
                refine ⟨3095864477840520971916803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063909651893680647944535 3095864477840520971916803)
                ·
                  refine ⟨4643796716760781457875205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095864477840520971916803 4643796716760781457875205)
                  ·
                    refine ⟨870711884392646523351601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4643796716760781457875205 870711884392646523351601)
                    ·
                      refine ⟨653033913294484892513701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870711884392646523351601 653033913294484892513701)
                      ·
                        rfl

theorem cell23_1271779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_1271779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271779 prefixEnd_1271779 := by exact prefixLift 1271779
  have htrace : WordTrace (prefixWord ++ tailWord_1271779) baseStart_1271779 baseEnd_1271779 := by
    simpa [prefixWord, tailWord_1271779, baseEnd_1271779] using wordTrace_append hprefix tailTrace_1271779
  have hstable : (prefixWord ++ tailWord_1271779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271779).length < 2 ^ (prefixWord ++ tailWord_1271779).sum := by decide
  have hdescent : baseEnd_1271779 < baseStart_1271779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271795 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 3]
def baseStart_1271795 : Nat := 118140960795 + 1271795 * 2 ^ 59
def prefixEnd_1271795 : Nat := 4983230072969 + 3 ^ 40 * 1271795 * 2
def baseEnd_1271795 : Nat := 653042128984956829913627

theorem tailTrace_1271795 : CollatzResearch.WordTrace tailWord_1271795 prefixEnd_1271795 653042128984956829913627 := by
  unfold tailWord_1271795
  simp only [CollatzResearch.WordTrace]
  refine ⟨46386174427511395138512839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30924116285007596759008559 46386174427511395138512839)
  ·
    refine ⟨69579261641267092707769259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46386174427511395138512839 69579261641267092707769259)
    ·
      refine ⟨104368892461900639061653889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69579261641267092707769259 104368892461900639061653889)
      ·
        refine ⟨78276669346425479296240417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104368892461900639061653889 78276669346425479296240417)
        ·
          refine ⟨58707502009819109472180313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78276669346425479296240417 58707502009819109472180313)
          ·
            refine ⟨44030626507364332104135235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58707502009819109472180313 44030626507364332104135235)
            ·
              refine ⟨66045939761046498156202853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44030626507364332104135235 66045939761046498156202853)
              ·
                refine ⟨12383613705196218404288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66045939761046498156202853 12383613705196218404288035)
                ·
                  refine ⟨18575420557794327606432053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12383613705196218404288035 18575420557794327606432053)
                  ·
                    refine ⟨1741445677293218213103005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18575420557794327606432053 1741445677293218213103005)
                    ·
                      refine ⟨653042128984956829913627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741445677293218213103005 653042128984956829913627)
                      ·
                        rfl

theorem cell23_1271795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 3].length) (baseStart_1271795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271795 prefixEnd_1271795 := by exact prefixLift 1271795
  have htrace : WordTrace (prefixWord ++ tailWord_1271795) baseStart_1271795 baseEnd_1271795 := by
    simpa [prefixWord, tailWord_1271795, baseEnd_1271795] using wordTrace_append hprefix tailTrace_1271795
  have hstable : (prefixWord ++ tailWord_1271795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271795).length < 2 ^ (prefixWord ++ tailWord_1271795).sum := by decide
  have hdescent : baseEnd_1271795 < baseStart_1271795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271819 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 5]
def baseStart_1271819 : Nat := 118140960795 + 1271819 * 2 ^ 59
def prefixEnd_1271819 : Nat := 4983230072969 + 3 ^ 40 * 1271819 * 2
def baseEnd_1271819 : Nat := 72561605835629415112613

theorem tailTrace_1271819 : CollatzResearch.WordTrace tailWord_1271819 prefixEnd_1271819 72561605835629415112613 := by
  unfold tailWord_1271819
  simp only [CollatzResearch.WordTrace]
  refine ⟨46387049779424447237386511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30924699852949631491591007 46387049779424447237386511)
  ·
    refine ⟨69580574669136670856079767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46387049779424447237386511 69580574669136670856079767)
    ·
      refine ⟨104370862003705006284119651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69580574669136670856079767 104370862003705006284119651)
      ·
        refine ⟨156556293005557509426179477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104370862003705006284119651 156556293005557509426179477)
        ·
          refine ⟨7338576234635508254352163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 156556293005557509426179477 7338576234635508254352163)
          ·
            refine ⟨11007864351953262381528245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7338576234635508254352163 11007864351953262381528245)
            ·
              refine ⟨1031987282995618348268273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11007864351953262381528245 1031987282995618348268273)
              ·
                refine ⟨773990462246713761201205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031987282995618348268273 773990462246713761201205)
                ·
                  refine ⟨72561605835629415112613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 773990462246713761201205 72561605835629415112613)
                  ·
                    rfl

theorem cell23_1271819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 5].length) (baseStart_1271819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271819 prefixEnd_1271819 := by exact prefixLift 1271819
  have htrace : WordTrace (prefixWord ++ tailWord_1271819) baseStart_1271819 baseEnd_1271819 := by
    simpa [prefixWord, tailWord_1271819, baseEnd_1271819] using wordTrace_append hprefix tailTrace_1271819
  have hstable : (prefixWord ++ tailWord_1271819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271819).length < 2 ^ (prefixWord ++ tailWord_1271819).sum := by decide
  have hdescent : baseEnd_1271819 < baseStart_1271819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271835 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4]
def baseStart_1271835 : Nat := 118140960795 + 1271835 * 2 ^ 59
def prefixEnd_1271835 : Nat := 4983230072969 + 3 ^ 40 * 1271835 * 2
def baseEnd_1271835 : Nat := 653062668211136673413443

theorem tailTrace_1271835 : CollatzResearch.WordTrace tailWord_1271835 prefixEnd_1271835 653062668211136673413443 := by
  unfold tailWord_1271835
  simp only [CollatzResearch.WordTrace]
  refine ⟨46387633347366481969968959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30925088898244321313312639 46387633347366481969968959)
  ·
    refine ⟨69581450021049722954953439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46387633347366481969968959 69581450021049722954953439)
    ·
      refine ⟨104372175031574584432430159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69581450021049722954953439 104372175031574584432430159)
      ·
        refine ⟨156558262547361876648645239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104372175031574584432430159 156558262547361876648645239)
        ·
          refine ⟨234837393821042814972967859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156558262547361876648645239 234837393821042814972967859)
          ·
            refine ⟨352256090731564222459451789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234837393821042814972967859 352256090731564222459451789)
            ·
              refine ⟨132096034024336583422294421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352256090731564222459451789 132096034024336583422294421)
              ·
                refine ⟨6192001594890777347920051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132096034024336583422294421 6192001594890777347920051)
                ·
                  refine ⟨9288002392336166021880077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6192001594890777347920051 9288002392336166021880077)
                  ·
                    refine ⟨3483000897126062258205029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9288002392336166021880077 3483000897126062258205029)
                    ·
                      refine ⟨653062668211136673413443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3483000897126062258205029 653062668211136673413443)
                      ·
                        rfl

theorem cell23_1271835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_1271835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271835 prefixEnd_1271835 := by exact prefixLift 1271835
  have htrace : WordTrace (prefixWord ++ tailWord_1271835) baseStart_1271835 baseEnd_1271835 := by
    simpa [prefixWord, tailWord_1271835, baseEnd_1271835] using wordTrace_append hprefix tailTrace_1271835
  have hstable : (prefixWord ++ tailWord_1271835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271835).length < 2 ^ (prefixWord ++ tailWord_1271835).sum := by decide
  have hdescent : baseEnd_1271835 < baseStart_1271835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271852 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 3, 6, 2]
def baseStart_1271852 : Nat := 118140960795 + 1271852 * 2 ^ 59
def prefixEnd_1271852 : Nat := 4983230072969 + 3 ^ 40 * 1271852 * 2
def baseEnd_1271852 : Nat := 653071397382263106900865

theorem tailTrace_1271852 : CollatzResearch.WordTrace tailWord_1271852 prefixEnd_1271852 653071397382263106900865 := by
  unfold tailWord_1271852
  simp only [CollatzResearch.WordTrace]
  refine ⟨23194126694152446936668905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30925502258869929248891873 23194126694152446936668905)
  ·
    refine ⟨17395595020614335202501679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23194126694152446936668905 17395595020614335202501679)
    ·
      refine ⟨26093392530921502803752519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17395595020614335202501679 26093392530921502803752519)
      ·
        refine ⟨39140088796382254205628779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26093392530921502803752519 39140088796382254205628779)
        ·
          refine ⟨58710133194573381308443169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39140088796382254205628779 58710133194573381308443169)
          ·
            refine ⟨44032599895930035981332377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58710133194573381308443169 44032599895930035981332377)
            ·
              refine ⟨33024449921947526985999283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44032599895930035981332377 33024449921947526985999283)
              ·
                refine ⟨49536674882921290478998925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33024449921947526985999283 49536674882921290478998925)
                ·
                  refine ⟨18576253081095483929624597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49536674882921290478998925 18576253081095483929624597)
                  ·
                    refine ⟨870761863176350809201153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18576253081095483929624597 870761863176350809201153)
                    ·
                      refine ⟨653071397382263106900865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870761863176350809201153 653071397382263106900865)
                      ·
                        rfl

theorem cell23_1271852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_1271852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271852 prefixEnd_1271852 := by exact prefixLift 1271852
  have htrace : WordTrace (prefixWord ++ tailWord_1271852) baseStart_1271852 baseEnd_1271852 := by
    simpa [prefixWord, tailWord_1271852, baseEnd_1271852] using wordTrace_append hprefix tailTrace_1271852
  have hstable : (prefixWord ++ tailWord_1271852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271852).length < 2 ^ (prefixWord ++ tailWord_1271852).sum := by decide
  have hdescent : baseEnd_1271852 < baseStart_1271852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271869 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_1271869 : Nat := 118140960795 + 1271869 * 2 ^ 59
def prefixEnd_1271869 : Nat := 4983230072969 + 3 ^ 40 * 1271869 * 2
def baseEnd_1271869 : Nat := 653080126553389540388287

theorem tailTrace_1271869 : CollatzResearch.WordTrace tailWord_1271869 prefixEnd_1271869 653080126553389540388287 := by
  unfold tailWord_1271869
  simp only [CollatzResearch.WordTrace]
  refine ⟨46388873429243305776706661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30925915619495537184471107 46388873429243305776706661)
  ·
    refine ⟨8697913767983119833132499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46388873429243305776706661 8697913767983119833132499)
    ·
      refine ⟨13046870651974679749698749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8697913767983119833132499 13046870651974679749698749)
      ·
        refine ⟨4892576494490504906137031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13046870651974679749698749 4892576494490504906137031)
        ·
          refine ⟨7338864741735757359205547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4892576494490504906137031 7338864741735757359205547)
          ·
            refine ⟨11008297112603636038808321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7338864741735757359205547 11008297112603636038808321)
            ·
              refine ⟨8256222834452727029106241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11008297112603636038808321 8256222834452727029106241)
              ·
                refine ⟨6192167125839545271829681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8256222834452727029106241 6192167125839545271829681)
                ·
                  refine ⟨4644125344379658953872261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192167125839545271829681 4644125344379658953872261)
                  ·
                    refine ⟨870773502071186053851049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644125344379658953872261 870773502071186053851049)
                    ·
                      refine ⟨653080126553389540388287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 870773502071186053851049 653080126553389540388287)
                      ·
                        rfl

theorem cell23_1271869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_1271869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271869 prefixEnd_1271869 := by exact prefixLift 1271869
  have htrace : WordTrace (prefixWord ++ tailWord_1271869) baseStart_1271869 baseEnd_1271869 := by
    simpa [prefixWord, tailWord_1271869, baseEnd_1271869] using wordTrace_append hprefix tailTrace_1271869
  have hstable : (prefixWord ++ tailWord_1271869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271869).length < 2 ^ (prefixWord ++ tailWord_1271869).sum := by decide
  have hdescent : baseEnd_1271869 < baseStart_1271869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271870 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_1271870 : Nat := 118140960795 + 1271870 * 2 ^ 59
def prefixEnd_1271870 : Nat := 4983230072969 + 3 ^ 40 * 1271870 * 2
def baseEnd_1271870 : Nat := 72564515559338226275087

theorem tailTrace_1271870 : CollatzResearch.WordTrace tailWord_1271870 prefixEnd_1271870 72564515559338226275087 := by
  unfold tailWord_1271870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798613737779960368436633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30925939934826455298328709 5798613737779960368436633)
  ·
    refine ⟨4348960303334970276327475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5798613737779960368436633 4348960303334970276327475)
    ·
      refine ⟨6523440455002455414491213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4348960303334970276327475 6523440455002455414491213)
      ·
        refine ⟨2446290170625920780434205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6523440455002455414491213 2446290170625920780434205)
        ·
          refine ⟨917358813984720292662827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2446290170625920780434205 917358813984720292662827)
          ·
            refine ⟨1376038220977080438994241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917358813984720292662827 1376038220977080438994241)
            ·
              refine ⟨1032028665732810329245681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376038220977080438994241 1032028665732810329245681)
              ·
                refine ⟨774021499299607746934261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032028665732810329245681 774021499299607746934261)
                ·
                  refine ⟨72564515559338226275087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 774021499299607746934261 72564515559338226275087)
                  ·
                    rfl

theorem cell23_1271870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_1271870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271870 prefixEnd_1271870 := by exact prefixLift 1271870
  have htrace : WordTrace (prefixWord ++ tailWord_1271870) baseStart_1271870 baseEnd_1271870 := by
    simpa [prefixWord, tailWord_1271870, baseEnd_1271870] using wordTrace_append hprefix tailTrace_1271870
  have hstable : (prefixWord ++ tailWord_1271870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271870).length < 2 ^ (prefixWord ++ tailWord_1271870).sum := by decide
  have hdescent : baseEnd_1271870 < baseStart_1271870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271906 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1271906 : Nat := 118140960795 + 1271906 * 2 ^ 59
def prefixEnd_1271906 : Nat := 4983230072969 + 3 ^ 40 * 1271906 * 2
def baseEnd_1271906 : Nat := 653099125337605895625617

theorem tailTrace_1271906 : CollatzResearch.WordTrace tailWord_1271906 prefixEnd_1271906 653099125337605895625617 := by
  unfold tailWord_1271906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11597555732527315273950893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30926815286739507397202381 11597555732527315273950893)
  ·
    refine ⟨4349083399697743227731585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11597555732527315273950893 4349083399697743227731585)
    ·
      refine ⟨3261812549773307420798689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4349083399697743227731585 3261812549773307420798689)
      ·
        refine ⟨2446359412329980565599017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3261812549773307420798689 2446359412329980565599017)
        ·
          refine ⟨1834769559247485424199263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2446359412329980565599017 1834769559247485424199263)
          ·
            refine ⟨2752154338871228136298895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834769559247485424199263 2752154338871228136298895)
            ·
              refine ⟨4128231508306842204448343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752154338871228136298895 4128231508306842204448343)
              ·
                refine ⟨6192347262460263306672515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128231508306842204448343 6192347262460263306672515)
                ·
                  refine ⟨9288520893690394960008773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6192347262460263306672515 9288520893690394960008773)
                  ·
                    refine ⟨1741597667566949055001645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9288520893690394960008773 1741597667566949055001645)
                    ·
                      refine ⟨653099125337605895625617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1741597667566949055001645 653099125337605895625617)
                      ·
                        rfl

theorem cell23_1271906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1271906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271906 prefixEnd_1271906 := by exact prefixLift 1271906
  have htrace : WordTrace (prefixWord ++ tailWord_1271906) baseStart_1271906 baseEnd_1271906 := by
    simpa [prefixWord, tailWord_1271906, baseEnd_1271906] using wordTrace_append hprefix tailTrace_1271906
  have hstable : (prefixWord ++ tailWord_1271906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271906).length < 2 ^ (prefixWord ++ tailWord_1271906).sum := by decide
  have hdescent : baseEnd_1271906 < baseStart_1271906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271926 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1271926 : Nat := 118140960795 + 1271926 * 2 ^ 59
def prefixEnd_1271926 : Nat := 4983230072969 + 3 ^ 40 * 1271926 * 2
def baseEnd_1271926 : Nat := 72567710550077313041725

theorem tailTrace_1271926 : CollatzResearch.WordTrace tailWord_1271926 prefixEnd_1271926 72567710550077313041725 := by
  unfold tailWord_1271926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899434524377300281970727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30927301593357869674354421 2899434524377300281970727)
  ·
    refine ⟨4349151786565950422956091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899434524377300281970727 4349151786565950422956091)
    ·
      refine ⟨6523727679848925634434137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4349151786565950422956091 6523727679848925634434137)
      ·
        refine ⟨4892795759886694225825603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6523727679848925634434137 4892795759886694225825603)
        ·
          refine ⟨7339193639830041338738405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4892795759886694225825603 7339193639830041338738405)
          ·
            refine ⟨1376098807468132751013451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7339193639830041338738405 1376098807468132751013451)
            ·
              refine ⟨2064148211202199126520177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376098807468132751013451 2064148211202199126520177)
              ·
                refine ⟨1548111158401649344890133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064148211202199126520177 1548111158401649344890133)
                ·
                  refine ⟨72567710550077313041725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1548111158401649344890133 72567710550077313041725)
                  ·
                    rfl

theorem cell23_1271926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1271926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271926 prefixEnd_1271926 := by exact prefixLift 1271926
  have htrace : WordTrace (prefixWord ++ tailWord_1271926) baseStart_1271926 baseEnd_1271926 := by
    simpa [prefixWord, tailWord_1271926, baseEnd_1271926] using wordTrace_append hprefix tailTrace_1271926
  have hstable : (prefixWord ++ tailWord_1271926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271926).length < 2 ^ (prefixWord ++ tailWord_1271926).sum := by decide
  have hdescent : baseEnd_1271926 < baseStart_1271926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271935 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 12]
def baseStart_1271935 : Nat := 118140960795 + 1271935 * 2 ^ 59
def prefixEnd_1271935 : Nat := 4983230072969 + 3 ^ 40 * 1271935 * 2
def baseEnd_1271935 : Nat := 217704672092195427387661

theorem tailTrace_1271935 : CollatzResearch.WordTrace tailWord_1271935 prefixEnd_1271935 217704672092195427387661 := by
  unfold tailWord_1271935
  simp only [CollatzResearch.WordTrace]
  refine ⟨46391280647004199048609259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30927520431336132699072839 46391280647004199048609259)
  ·
    refine ⟨69586920970506298572913889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46391280647004199048609259 69586920970506298572913889)
    ·
      refine ⟨52190190727879723929685417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69586920970506298572913889 52190190727879723929685417)
      ·
        refine ⟨39142643045909792947264063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52190190727879723929685417 39142643045909792947264063)
        ·
          refine ⟨58713964568864689420896095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39142643045909792947264063 58713964568864689420896095)
          ·
            refine ⟨88070946853297034131344143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58713964568864689420896095 88070946853297034131344143)
            ·
              refine ⟨132106420279945551197016215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88070946853297034131344143 132106420279945551197016215)
              ·
                refine ⟨198159630419918326795524323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132106420279945551197016215 198159630419918326795524323)
                ·
                  refine ⟨297239445629877490193286485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198159630419918326795524323 297239445629877490193286485)
                  ·
                    refine ⟨217704672092195427387661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 297239445629877490193286485 217704672092195427387661)
                    ·
                      rfl

theorem cell23_1271935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_1271935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1271935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1271935 prefixEnd_1271935 := by exact prefixLift 1271935
  have htrace : WordTrace (prefixWord ++ tailWord_1271935) baseStart_1271935 baseEnd_1271935 := by
    simpa [prefixWord, tailWord_1271935, baseEnd_1271935] using wordTrace_append hprefix tailTrace_1271935
  have hstable : (prefixWord ++ tailWord_1271935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271935).length < 2 ^ (prefixWord ++ tailWord_1271935).sum := by decide
  have hdescent : baseEnd_1271935 < baseStart_1271935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
