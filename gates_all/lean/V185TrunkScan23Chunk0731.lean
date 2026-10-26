import V185TrunkScan23Chunk0730

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4323357 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4323357 : Nat := 118140960795 + 4323357 * 2 ^ 59
def prefixEnd_4323357 : Nat := 4983230072969 + 3 ^ 40 * 4323357 * 2
def baseEnd_4323357 : Nat := 2219960181980346579554749

theorem tailTrace_4323357 : CollatzResearch.WordTrace tailWord_4323357 prefixEnd_4323357 2219960181980346579554749 := by
  unfold tailWord_4323357
  simp only [CollatzResearch.WordTrace]
  refine ⟨157685784198223434436024325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105123856132148956290682883 157685784198223434436024325)
  ·
    refine ⟨29566084537166893956754561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157685784198223434436024325 29566084537166893956754561)
    ·
      refine ⟨22174563402875170467565921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29566084537166893956754561 22174563402875170467565921)
      ·
        refine ⟨16630922552156377850674441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22174563402875170467565921 16630922552156377850674441)
        ·
          refine ⟨12473191914117283388005831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16630922552156377850674441 12473191914117283388005831)
          ·
            refine ⟨18709787871175925082008747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12473191914117283388005831 18709787871175925082008747)
            ·
              refine ⟨28064681806763887623013121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18709787871175925082008747 28064681806763887623013121)
              ·
                refine ⟨21048511355072915717259841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28064681806763887623013121 21048511355072915717259841)
                ·
                  refine ⟨15786383516304686787944881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21048511355072915717259841 15786383516304686787944881)
                  ·
                    refine ⟨11839787637228515090958661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15786383516304686787944881 11839787637228515090958661)
                    ·
                      refine ⟨2219960181980346579554749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11839787637228515090958661 2219960181980346579554749)
                      ·
                        rfl

theorem cell23_4323357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4323357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323357 prefixEnd_4323357 := by exact prefixLift 4323357
  have htrace : WordTrace (prefixWord ++ tailWord_4323357) baseStart_4323357 baseEnd_4323357 := by
    simpa [prefixWord, tailWord_4323357, baseEnd_4323357] using wordTrace_append hprefix tailTrace_4323357
  have hstable : (prefixWord ++ tailWord_4323357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323357).length < 2 ^ (prefixWord ++ tailWord_4323357).sum := by decide
  have hdescent : baseEnd_4323357 < baseStart_4323357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323361 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_4323361 : Nat := 118140960795 + 4323361 * 2 ^ 59
def prefixEnd_4323361 : Nat := 4983230072969 + 3 ^ 40 * 4323361 * 2
def baseEnd_4323361 : Nat := 2219962235902964563904731

theorem tailTrace_4323361 : CollatzResearch.WordTrace tailWord_4323361 prefixEnd_4323361 2219962235902964563904731 := by
  unfold tailWord_4323361
  simp only [CollatzResearch.WordTrace]
  refine ⟨157685930090208943119169937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105123953393472628746113291 157685930090208943119169937)
  ·
    refine ⟨118264447567656707339377453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157685930090208943119169937 118264447567656707339377453)
    ·
      refine ⟨44349167837871265252266545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118264447567656707339377453 44349167837871265252266545)
      ·
        refine ⟨33261875878403448939199909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44349167837871265252266545 33261875878403448939199909)
        ·
          refine ⟨6236601727200646676099983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33261875878403448939199909 6236601727200646676099983)
          ·
            refine ⟨9354902590800970014149975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6236601727200646676099983 9354902590800970014149975)
            ·
              refine ⟨14032353886201455021224963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9354902590800970014149975 14032353886201455021224963)
              ·
                refine ⟨21048530829302182531837445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14032353886201455021224963 21048530829302182531837445)
                ·
                  refine ⟨3946599530494159224719521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21048530829302182531837445 3946599530494159224719521)
                  ·
                    refine ⟨2959949647870619418539641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3946599530494159224719521 2959949647870619418539641)
                    ·
                      refine ⟨2219962235902964563904731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959949647870619418539641 2219962235902964563904731)
                      ·
                        rfl

theorem cell23_4323361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_4323361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323361 prefixEnd_4323361 := by exact prefixLift 4323361
  have htrace : WordTrace (prefixWord ++ tailWord_4323361) baseStart_4323361 baseEnd_4323361 := by
    simpa [prefixWord, tailWord_4323361, baseEnd_4323361] using wordTrace_append hprefix tailTrace_4323361
  have hstable : (prefixWord ++ tailWord_4323361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323361).length < 2 ^ (prefixWord ++ tailWord_4323361).sum := by decide
  have hdescent : baseEnd_4323361 < baseStart_4323361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323377 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 3]
def baseStart_4323377 : Nat := 118140960795 + 4323377 * 2 ^ 59
def prefixEnd_4323377 : Nat := 4983230072969 + 3 ^ 40 * 4323377 * 2
def baseEnd_4323377 : Nat := 2219970451593436501304657

theorem tailTrace_4323377 : CollatzResearch.WordTrace tailWord_4323377 prefixEnd_4323377 2219970451593436501304657 := by
  unfold tailWord_4323377
  simp only [CollatzResearch.WordTrace]
  refine ⟨157686513658150977851752385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105124342438767318567834923 157686513658150977851752385)
  ·
    refine ⟨118264885243613233388814289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157686513658150977851752385 118264885243613233388814289)
    ·
      refine ⟨88698663932709925041610717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118264885243613233388814289 88698663932709925041610717)
      ·
        refine ⟨33261998974766221890604019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88698663932709925041610717 33261998974766221890604019)
        ·
          refine ⟨49892998462149332835906029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33261998974766221890604019 49892998462149332835906029)
          ·
            refine ⟨18709874423305999813464761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49892998462149332835906029 18709874423305999813464761)
            ·
              refine ⟨14032405817479499860098571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18709874423305999813464761 14032405817479499860098571)
              ·
                refine ⟨21048608726219249790147857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14032405817479499860098571 21048608726219249790147857)
                ·
                  refine ⟨15786456544664437342610893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21048608726219249790147857 15786456544664437342610893)
                  ·
                    refine ⟨5919921204249164003479085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15786456544664437342610893 5919921204249164003479085)
                    ·
                      refine ⟨2219970451593436501304657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5919921204249164003479085 2219970451593436501304657)
                      ·
                        rfl

theorem cell23_4323377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_4323377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323377 prefixEnd_4323377 := by exact prefixLift 4323377
  have htrace : WordTrace (prefixWord ++ tailWord_4323377) baseStart_4323377 baseEnd_4323377 := by
    simpa [prefixWord, tailWord_4323377, baseEnd_4323377] using wordTrace_append hprefix tailTrace_4323377
  have hstable : (prefixWord ++ tailWord_4323377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323377).length < 2 ^ (prefixWord ++ tailWord_4323377).sum := by decide
  have hdescent : baseEnd_4323377 < baseStart_4323377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323378 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_4323378 : Nat := 118140960795 + 4323378 * 2 ^ 59
def prefixEnd_4323378 : Nat := 4983230072969 + 3 ^ 40 * 4323378 * 2
def baseEnd_4323378 : Nat := 2219970965074090997392153

theorem tailTrace_4323378 : CollatzResearch.WordTrace tailWord_4323378 prefixEnd_4323378 2219970965074090997392153 := by
  unfold tailWord_4323378
  simp only [CollatzResearch.WordTrace]
  refine ⟨39421637532786838755634697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105124366754098236681692525 39421637532786838755634697)
  ·
    refine ⟨29566228149590129066726023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39421637532786838755634697 29566228149590129066726023)
    ·
      refine ⟨44349342224385193600089035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29566228149590129066726023 44349342224385193600089035)
      ·
        refine ⟨66524013336577790400133553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44349342224385193600089035 66524013336577790400133553)
        ·
          refine ⟨49893010002433342800100165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66524013336577790400133553 49893010002433342800100165)
          ·
            refine ⟨9354939375456251775018781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49893010002433342800100165 9354939375456251775018781)
            ·
              refine ⟨3508102265796094415632043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9354939375456251775018781 3508102265796094415632043)
              ·
                refine ⟨5262153398694141623448065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508102265796094415632043 5262153398694141623448065)
                ·
                  refine ⟨3946615049020606217586049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5262153398694141623448065 3946615049020606217586049)
                  ·
                    refine ⟨2959961286765454663189537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3946615049020606217586049 2959961286765454663189537)
                    ·
                      refine ⟨2219970965074090997392153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2959961286765454663189537 2219970965074090997392153)
                      ·
                        rfl

theorem cell23_4323378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_4323378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323378 prefixEnd_4323378 := by exact prefixLift 4323378
  have htrace : WordTrace (prefixWord ++ tailWord_4323378) baseStart_4323378 baseEnd_4323378 := by
    simpa [prefixWord, tailWord_4323378, baseEnd_4323378] using wordTrace_append hprefix tailTrace_4323378
  have hstable : (prefixWord ++ tailWord_4323378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323378).length < 2 ^ (prefixWord ++ tailWord_4323378).sum := by decide
  have hdescent : baseEnd_4323378 < baseStart_4323378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323417 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_4323417 : Nat := 118140960795 + 4323417 * 2 ^ 59
def prefixEnd_4323417 : Nat := 4983230072969 + 3 ^ 40 * 4323417 * 2
def baseEnd_4323417 : Nat := 2219990990819616344804473

theorem tailTrace_4323417 : CollatzResearch.WordTrace tailWord_4323417 prefixEnd_4323417 2219990990819616344804473 := by
  unfold tailWord_4323417
  simp only [CollatzResearch.WordTrace]
  refine ⟨157687972578006064683208505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105125315052004043122139003 157687972578006064683208505)
  ·
    refine ⟨118265979433504548512406379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157687972578006064683208505 118265979433504548512406379)
    ·
      refine ⟨177398969150256822768609569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118265979433504548512406379 177398969150256822768609569)
      ·
        refine ⟨133049226862692617076457177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177398969150256822768609569 133049226862692617076457177)
        ·
          refine ⟨99786920147019462807342883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133049226862692617076457177 99786920147019462807342883)
          ·
            refine ⟨149680380220529194211014325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99786920147019462807342883 149680380220529194211014325)
            ·
              refine ⟨14032535645674611957282593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149680380220529194211014325 14032535645674611957282593)
              ·
                refine ⟨10524401734255958967961945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14032535645674611957282593 10524401734255958967961945)
                ·
                  refine ⟨7893301300691969225971459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10524401734255958967961945 7893301300691969225971459)
                  ·
                    refine ⟨11839951951037953838957189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7893301300691969225971459 11839951951037953838957189)
                    ·
                      refine ⟨2219990990819616344804473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11839951951037953838957189 2219990990819616344804473)
                      ·
                        rfl

theorem cell23_4323417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_4323417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323417 prefixEnd_4323417 := by exact prefixLift 4323417
  have htrace : WordTrace (prefixWord ++ tailWord_4323417) baseStart_4323417 baseEnd_4323417 := by
    simpa [prefixWord, tailWord_4323417, baseEnd_4323417] using wordTrace_append hprefix tailTrace_4323417
  have hstable : (prefixWord ++ tailWord_4323417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323417).length < 2 ^ (prefixWord ++ tailWord_4323417).sum := by decide
  have hdescent : baseEnd_4323417 < baseStart_4323417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323474 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_4323474 : Nat := 118140960795 + 4323474 * 2 ^ 59
def prefixEnd_4323474 : Nat := 4983230072969 + 3 ^ 40 * 4323474 * 2
def baseEnd_4323474 : Nat := 246668917690769180199079

theorem tailTrace_4323474 : CollatzResearch.WordTrace tailWord_4323474 prefixEnd_4323474 246668917690769180199079 := by
  unfold tailWord_4323474
  simp only [CollatzResearch.WordTrace]
  refine ⟨39422512884699890854508369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105126701025866375612022317 39422512884699890854508369)
  ·
    refine ⟨29566884663524918140881277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39422512884699890854508369 29566884663524918140881277)
    ·
      refine ⟨11087581748821844302830479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29566884663524918140881277 11087581748821844302830479)
      ·
        refine ⟨16631372623232766454245719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11087581748821844302830479 16631372623232766454245719)
        ·
          refine ⟨24947058934849149681368579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16631372623232766454245719 24947058934849149681368579)
          ·
            refine ⟨37420588402273724522052869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24947058934849149681368579 37420588402273724522052869)
            ·
              refine ⟨7016360325426323347884913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37420588402273724522052869 7016360325426323347884913)
              ·
                refine ⟨5262270244069742510913685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7016360325426323347884913 5262270244069742510913685)
                ·
                  refine ⟨246668917690769180199079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5262270244069742510913685 246668917690769180199079)
                  ·
                    rfl

theorem cell23_4323474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_4323474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323474 prefixEnd_4323474 := by exact prefixLift 4323474
  have htrace : WordTrace (prefixWord ++ tailWord_4323474) baseStart_4323474 baseEnd_4323474 := by
    simpa [prefixWord, tailWord_4323474, baseEnd_4323474] using wordTrace_append hprefix tailTrace_4323474
  have hstable : (prefixWord ++ tailWord_4323474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323474).length < 2 ^ (prefixWord ++ tailWord_4323474).sum := by decide
  have hdescent : baseEnd_4323474 < baseStart_4323474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323501 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_4323501 : Nat := 118140960795 + 4323501 * 2 ^ 59
def prefixEnd_4323501 : Nat := 4983230072969 + 3 ^ 40 * 4323501 * 2
def baseEnd_4323501 : Nat := 2220034123194594016154087

theorem tailTrace_4323501 : CollatzResearch.WordTrace tailWord_4323501 prefixEnd_4323501 2220034123194594016154087 := by
  unfold tailWord_4323501
  simp only [CollatzResearch.WordTrace]
  refine ⟨157691036309701747029266357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105127357539801164686177571 157691036309701747029266357)
  ·
    refine ⟨14783534654034538783993721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157691036309701747029266357 14783534654034538783993721)
    ·
      refine ⟨11087650990525904087995291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14783534654034538783993721 11087650990525904087995291)
      ·
        refine ⟨16631476485788856131992937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11087650990525904087995291 16631476485788856131992937)
        ·
          refine ⟨12473607364341642098994703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16631476485788856131992937 12473607364341642098994703)
          ·
            refine ⟨18710411046512463148492055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12473607364341642098994703 18710411046512463148492055)
            ·
              refine ⟨28065616569768694722738083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18710411046512463148492055 28065616569768694722738083)
              ·
                refine ⟨42098424854653042084107125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28065616569768694722738083 42098424854653042084107125)
                ·
                  refine ⟨3946727330123722695385043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42098424854653042084107125 3946727330123722695385043)
                  ·
                    refine ⟨5920090995185584043077565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3946727330123722695385043 5920090995185584043077565)
                    ·
                      refine ⟨2220034123194594016154087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5920090995185584043077565 2220034123194594016154087)
                      ·
                        rfl

theorem cell23_4323501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_4323501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323501 prefixEnd_4323501 := by exact prefixLift 4323501
  have htrace : WordTrace (prefixWord ++ tailWord_4323501) baseStart_4323501 baseEnd_4323501 := by
    simpa [prefixWord, tailWord_4323501, baseEnd_4323501] using wordTrace_append hprefix tailTrace_4323501
  have hstable : (prefixWord ++ tailWord_4323501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323501).length < 2 ^ (prefixWord ++ tailWord_4323501).sum := by decide
  have hdescent : baseEnd_4323501 < baseStart_4323501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323511 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 2, 3, 2]
def baseStart_4323511 : Nat := 118140960795 + 4323511 * 2 ^ 59
def prefixEnd_4323511 : Nat := 4983230072969 + 3 ^ 40 * 4323511 * 2
def baseEnd_4323511 : Nat := 2220039258001138977029041

theorem tailTrace_4323511 : CollatzResearch.WordTrace tailWord_4323511 prefixEnd_4323511 2220039258001138977029041 := by
  unfold tailWord_4323511
  simp only [CollatzResearch.WordTrace]
  refine ⟨157691401039665518737130387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105127600693110345824753591 157691401039665518737130387)
  ·
    refine ⟨236537101559498278105695581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157691401039665518737130387 236537101559498278105695581)
    ·
      refine ⟨88701413084811854289635843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236537101559498278105695581 88701413084811854289635843)
      ·
        refine ⟨133052119627217781434453765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88701413084811854289635843 133052119627217781434453765)
        ·
          refine ⟨24947272430103334018960081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133052119627217781434453765 24947272430103334018960081)
          ·
            refine ⟨18710454322577500514220061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24947272430103334018960081 18710454322577500514220061)
            ·
              refine ⟨7016420370966562692832523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18710454322577500514220061 7016420370966562692832523)
              ·
                refine ⟨10524630556449844039248785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7016420370966562692832523 10524630556449844039248785)
                ·
                  refine ⟨7893472917337383029436589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10524630556449844039248785 7893472917337383029436589)
                  ·
                    refine ⟨2960052344001518636038721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7893472917337383029436589 2960052344001518636038721)
                    ·
                      refine ⟨2220039258001138977029041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960052344001518636038721 2220039258001138977029041)
                      ·
                        rfl

theorem cell23_4323511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_4323511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323511 prefixEnd_4323511 := by exact prefixLift 4323511
  have htrace : WordTrace (prefixWord ++ tailWord_4323511) baseStart_4323511 baseEnd_4323511 := by
    simpa [prefixWord, tailWord_4323511, baseEnd_4323511] using wordTrace_append hprefix tailTrace_4323511
  have hstable : (prefixWord ++ tailWord_4323511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323511).length < 2 ^ (prefixWord ++ tailWord_4323511).sum := by decide
  have hdescent : baseEnd_4323511 < baseStart_4323511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323537 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_4323537 : Nat := 118140960795 + 4323537 * 2 ^ 59
def prefixEnd_4323537 : Nat := 4983230072969 + 3 ^ 40 * 4323537 * 2
def baseEnd_4323537 : Nat := 2220052608498155875303921

theorem tailTrace_4323537 : CollatzResearch.WordTrace tailWord_4323537 prefixEnd_4323537 2220052608498155875303921 := by
  unfold tailWord_4323537
  simp only [CollatzResearch.WordTrace]
  refine ⟨157692349337571325177576865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105128232891714216785051243 157692349337571325177576865)
  ·
    refine ⟨118269262003178493883182649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157692349337571325177576865 118269262003178493883182649)
    ·
      refine ⟨88701946502383870412386987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118269262003178493883182649 88701946502383870412386987)
      ·
        refine ⟨133052919753575805618580481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88701946502383870412386987 133052919753575805618580481)
        ·
          refine ⟨99789689815181854213935361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133052919753575805618580481 99789689815181854213935361)
          ·
            refine ⟨74842267361386390660451521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99789689815181854213935361 74842267361386390660451521)
            ·
              refine ⟨56131700521039792995338641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74842267361386390660451521 56131700521039792995338641)
              ·
                refine ⟨42098775390779844746503981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56131700521039792995338641 42098775390779844746503981)
                ·
                  refine ⟨15787040771542441779938993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42098775390779844746503981 15787040771542441779938993)
                  ·
                    refine ⟨11840280578656831334954245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15787040771542441779938993 11840280578656831334954245)
                    ·
                      refine ⟨2220052608498155875303921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11840280578656831334954245 2220052608498155875303921)
                      ·
                        rfl

theorem cell23_4323537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_4323537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323537 prefixEnd_4323537 := by exact prefixLift 4323537
  have htrace : WordTrace (prefixWord ++ tailWord_4323537) baseStart_4323537 baseEnd_4323537 := by
    simpa [prefixWord, tailWord_4323537, baseEnd_4323537] using wordTrace_append hprefix tailTrace_4323537
  have hstable : (prefixWord ++ tailWord_4323537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323537).length < 2 ^ (prefixWord ++ tailWord_4323537).sum := by decide
  have hdescent : baseEnd_4323537 < baseStart_4323537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323544 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_4323544 : Nat := 118140960795 + 4323544 * 2 ^ 59
def prefixEnd_4323544 : Nat := 4983230072969 + 3 ^ 40 * 4323544 * 2
def baseEnd_4323544 : Nat := 2220056202862737347916389

theorem tailTrace_4323544 : CollatzResearch.WordTrace tailWord_4323544 prefixEnd_4323544 2220056202862737347916389 := by
  unfold tailWord_4323544
  simp only [CollatzResearch.WordTrace]
  refine ⟨78846302324272982686540843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105128403099030643582054457 78846302324272982686540843)
  ·
    refine ⟨118269453486409474029811265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78846302324272982686540843 118269453486409474029811265)
    ·
      refine ⟨88702090114807105522358449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118269453486409474029811265 88702090114807105522358449)
      ·
        refine ⟨66526567586105329141768837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88702090114807105522358449 66526567586105329141768837)
        ·
          refine ⟨12473731422394749214081657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66526567586105329141768837 12473731422394749214081657)
          ·
            refine ⟨9355298566796061910561243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12473731422394749214081657 9355298566796061910561243)
            ·
              refine ⟨14032947850194092865841865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9355298566796061910561243 14032947850194092865841865)
              ·
                refine ⟨10524710887645569649381399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14032947850194092865841865 10524710887645569649381399)
                ·
                  refine ⟨15787066331468354474072099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10524710887645569649381399 15787066331468354474072099)
                  ·
                    refine ⟨23680599497202531711108149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15787066331468354474072099 23680599497202531711108149)
                    ·
                      refine ⟨2220056202862737347916389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23680599497202531711108149 2220056202862737347916389)
                      ·
                        rfl

theorem cell23_4323544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_4323544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323544 prefixEnd_4323544 := by exact prefixLift 4323544
  have htrace : WordTrace (prefixWord ++ tailWord_4323544) baseStart_4323544 baseEnd_4323544 := by
    simpa [prefixWord, tailWord_4323544, baseEnd_4323544] using wordTrace_append hprefix tailTrace_4323544
  have hstable : (prefixWord ++ tailWord_4323544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323544).length < 2 ^ (prefixWord ++ tailWord_4323544).sum := by decide
  have hdescent : baseEnd_4323544 < baseStart_4323544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323587 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_4323587 : Nat := 118140960795 + 4323587 * 2 ^ 59
def prefixEnd_4323587 : Nat := 4983230072969 + 3 ^ 40 * 4323587 * 2
def baseEnd_4323587 : Nat := 2220078282530880679678691

theorem tailTrace_4323587 : CollatzResearch.WordTrace tailWord_4323587 prefixEnd_4323587 2220078282530880679678691 := by
  unfold tailWord_4323587
  simp only [CollatzResearch.WordTrace]
  refine ⟨157694172987390183716897015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105129448658260122477931343 157694172987390183716897015)
  ·
    refine ⟨236541259481085275575345523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157694172987390183716897015 236541259481085275575345523)
    ·
      refine ⟨354811889221627913363018285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236541259481085275575345523 354811889221627913363018285)
      ·
        refine ⟨133054458458110467511131857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354811889221627913363018285 133054458458110467511131857)
        ·
          refine ⟨99790843843582850633348893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133054458458110467511131857 99790843843582850633348893)
          ·
            refine ⟨37421566441343568987505835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99790843843582850633348893 37421566441343568987505835)
            ·
              refine ⟨56132349662015353481258753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37421566441343568987505835 56132349662015353481258753)
              ·
                refine ⟨42099262246511515110944065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56132349662015353481258753 42099262246511515110944065)
                ·
                  refine ⟨31574446684883636333208049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42099262246511515110944065 31574446684883636333208049)
                  ·
                    refine ⟨23680835013662727249906037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31574446684883636333208049 23680835013662727249906037)
                    ·
                      refine ⟨2220078282530880679678691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23680835013662727249906037 2220078282530880679678691)
                      ·
                        rfl

theorem cell23_4323587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_4323587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323587 prefixEnd_4323587 := by exact prefixLift 4323587
  have htrace : WordTrace (prefixWord ++ tailWord_4323587) baseStart_4323587 baseEnd_4323587 := by
    simpa [prefixWord, tailWord_4323587, baseEnd_4323587] using wordTrace_append hprefix tailTrace_4323587
  have hstable : (prefixWord ++ tailWord_4323587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323587).length < 2 ^ (prefixWord ++ tailWord_4323587).sum := by decide
  have hdescent : baseEnd_4323587 < baseStart_4323587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323592 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_4323592 : Nat := 118140960795 + 4323592 * 2 ^ 59
def prefixEnd_4323592 : Nat := 4983230072969 + 3 ^ 40 * 4323592 * 2
def baseEnd_4323592 : Nat := 2220080849934153160116169

theorem tailTrace_4323592 : CollatzResearch.WordTrace tailWord_4323592 prefixEnd_4323592 2220080849934153160116169 := by
  unfold tailWord_4323592
  simp only [CollatzResearch.WordTrace]
  refine ⟨78847177676186034785414515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105129570234914713047219353 78847177676186034785414515)
  ·
    refine ⟨118270766514279052178121773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78847177676186034785414515 118270766514279052178121773)
    ·
      refine ⟨44351537442854644566795665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118270766514279052178121773 44351537442854644566795665)
      ·
        refine ⟨33263653082140983425096749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44351537442854644566795665 33263653082140983425096749)
        ·
          refine ⟨12473869905802868784411281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33263653082140983425096749 12473869905802868784411281)
          ·
            refine ⟨9355402429352151588308461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12473869905802868784411281 9355402429352151588308461)
            ·
              refine ⟨3508275911007056845615673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9355402429352151588308461 3508275911007056845615673)
              ·
                refine ⟨2631206933255292634211755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3508275911007056845615673 2631206933255292634211755)
                ·
                  refine ⟨3946810399882938951317633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631206933255292634211755 3946810399882938951317633)
                  ·
                    refine ⟨2960107799912204213488225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3946810399882938951317633 2960107799912204213488225)
                    ·
                      refine ⟨2220080849934153160116169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960107799912204213488225 2220080849934153160116169)
                      ·
                        rfl

theorem cell23_4323592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_4323592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323592 prefixEnd_4323592 := by exact prefixLift 4323592
  have htrace : WordTrace (prefixWord ++ tailWord_4323592) baseStart_4323592 baseEnd_4323592 := by
    simpa [prefixWord, tailWord_4323592, baseEnd_4323592] using wordTrace_append hprefix tailTrace_4323592
  have hstable : (prefixWord ++ tailWord_4323592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323592).length < 2 ^ (prefixWord ++ tailWord_4323592).sum := by decide
  have hdescent : baseEnd_4323592 < baseStart_4323592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323618 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_4323618 : Nat := 118140960795 + 4323618 * 2 ^ 59
def prefixEnd_4323618 : Nat := 4983230072969 + 3 ^ 40 * 4323618 * 2
def baseEnd_4323618 : Nat := 2220094200431170058391049

theorem tailTrace_4323618 : CollatzResearch.WordTrace tailWord_4323618 prefixEnd_4323618 2220094200431170058391049 := by
  unfold tailWord_4323618
  simp only [CollatzResearch.WordTrace]
  refine ⟨39423825912569469002818877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105130202433518584007517005 39423825912569469002818877)
  ·
    refine ⟨14783934717213550876057079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39423825912569469002818877 14783934717213550876057079)
    ·
      refine ⟨22175902075820326314085619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14783934717213550876057079 22175902075820326314085619)
      ·
        refine ⟨33263853113730489471128429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22175902075820326314085619 33263853113730489471128429)
        ·
          refine ⟨12473944917648933551673161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33263853113730489471128429 12473944917648933551673161)
          ·
            refine ⟨9355458688236700163754871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12473944917648933551673161 9355458688236700163754871)
            ·
              refine ⟨14033188032355050245632307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9355458688236700163754871 14033188032355050245632307)
              ·
                refine ⟨21049782048532575368448461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14033188032355050245632307 21049782048532575368448461)
                ·
                  refine ⟨7893668268199715763168173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21049782048532575368448461 7893668268199715763168173)
                  ·
                    refine ⟨2960125600574893411188065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7893668268199715763168173 2960125600574893411188065)
                    ·
                      refine ⟨2220094200431170058391049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960125600574893411188065 2220094200431170058391049)
                      ·
                        rfl

theorem cell23_4323618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_4323618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323618 prefixEnd_4323618 := by exact prefixLift 4323618
  have htrace : WordTrace (prefixWord ++ tailWord_4323618) baseStart_4323618 baseEnd_4323618 := by
    simpa [prefixWord, tailWord_4323618, baseEnd_4323618] using wordTrace_append hprefix tailTrace_4323618
  have hstable : (prefixWord ++ tailWord_4323618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323618).length < 2 ^ (prefixWord ++ tailWord_4323618).sum := by decide
  have hdescent : baseEnd_4323618 < baseStart_4323618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323631 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 6, 2, 2]
def baseStart_4323631 : Nat := 118140960795 + 4323631 * 2 ^ 59
def prefixEnd_4323631 : Nat := 4983230072969 + 3 ^ 40 * 4323631 * 2
def baseEnd_4323631 : Nat := 2220100875679678507528489

theorem tailTrace_4323631 : CollatzResearch.WordTrace tailWord_4323631 prefixEnd_4323631 2220100875679678507528489 := by
  unfold tailWord_4323631
  simp only [CollatzResearch.WordTrace]
  refine ⟨157695777799230779231498747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105130518532820519487665831 157695777799230779231498747)
  ·
    refine ⟨236543666698846168847248121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157695777799230779231498747 236543666698846168847248121)
    ·
      refine ⟨177407750024134626635436091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236543666698846168847248121 177407750024134626635436091)
      ·
        refine ⟨266111625036201939953154137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177407750024134626635436091 266111625036201939953154137)
        ·
          refine ⟨199583718777151454964865603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266111625036201939953154137 199583718777151454964865603)
          ·
            refine ⟨299375578165727182447298405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199583718777151454964865603 299375578165727182447298405)
            ·
              refine ⟨56132920906073846708868451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299375578165727182447298405 56132920906073846708868451)
              ·
                refine ⟨84199381359110770063302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56132920906073846708868451 84199381359110770063302677)
                ·
                  refine ⟨3946846001208317346717313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84199381359110770063302677 3946846001208317346717313)
                  ·
                    refine ⟨2960134500906238010037985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3946846001208317346717313 2960134500906238010037985)
                    ·
                      refine ⟨2220100875679678507528489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960134500906238010037985 2220100875679678507528489)
                      ·
                        rfl

theorem cell23_4323631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6, 2, 2].length) (baseStart_4323631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323631 prefixEnd_4323631 := by exact prefixLift 4323631
  have htrace : WordTrace (prefixWord ++ tailWord_4323631) baseStart_4323631 baseEnd_4323631 := by
    simpa [prefixWord, tailWord_4323631, baseEnd_4323631] using wordTrace_append hprefix tailTrace_4323631
  have hstable : (prefixWord ++ tailWord_4323631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323631).length < 2 ^ (prefixWord ++ tailWord_4323631).sum := by decide
  have hdescent : baseEnd_4323631 < baseStart_4323631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323644 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_4323644 : Nat := 118140960795 + 4323644 * 2 ^ 59
def prefixEnd_4323644 : Nat := 4983230072969 + 3 ^ 40 * 4323644 * 2
def baseEnd_4323644 : Nat := 2220107550928186956665929

theorem tailTrace_4323644 : CollatzResearch.WordTrace tailWord_4323644 prefixEnd_4323644 2220107550928186956665929 := by
  unfold tailWord_4323644
  simp only [CollatzResearch.WordTrace]
  refine ⟨78848125974091841225860993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105130834632122454967814657 78848125974091841225860993)
  ·
    refine ⟨59136094480568880919395745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78848125974091841225860993 59136094480568880919395745)
    ·
      refine ⟨44352070860426660689546809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59136094480568880919395745 44352070860426660689546809)
      ·
        refine ⟨33264053145319995517160107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44352070860426660689546809 33264053145319995517160107)
        ·
          refine ⟨49896079717979993275740161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33264053145319995517160107 49896079717979993275740161)
          ·
            refine ⟨37422059788484994956805121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49896079717979993275740161 37422059788484994956805121)
            ·
              refine ⟨28066544841363746217603841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37422059788484994956805121 28066544841363746217603841)
              ·
                refine ⟨21049908631022809663202881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28066544841363746217603841 21049908631022809663202881)
                ·
                  refine ⟨15787431473267107247402161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21049908631022809663202881 15787431473267107247402161)
                  ·
                    refine ⟨11840573604950330435551621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15787431473267107247402161 11840573604950330435551621)
                    ·
                      refine ⟨2220107550928186956665929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11840573604950330435551621 2220107550928186956665929)
                      ·
                        rfl

theorem cell23_4323644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_4323644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323644 prefixEnd_4323644 := by exact prefixLift 4323644
  have htrace : WordTrace (prefixWord ++ tailWord_4323644) baseStart_4323644 baseEnd_4323644 := by
    simpa [prefixWord, tailWord_4323644, baseEnd_4323644] using wordTrace_append hprefix tailTrace_4323644
  have hstable : (prefixWord ++ tailWord_4323644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323644).length < 2 ^ (prefixWord ++ tailWord_4323644).sum := by decide
  have hdescent : baseEnd_4323644 < baseStart_4323644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323657 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_4323657 : Nat := 118140960795 + 4323657 * 2 ^ 59
def prefixEnd_4323657 : Nat := 4983230072969 + 3 ^ 40 * 4323657 * 2
def baseEnd_4323657 : Nat := 2220114226176695405803369

theorem tailTrace_4323657 : CollatzResearch.WordTrace tailWord_4323657 prefixEnd_4323657 2220114226176695405803369 := by
  unfold tailWord_4323657
  simp only [CollatzResearch.WordTrace]
  refine ⟨157696726097136585671945225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105131150731424390447963483 157696726097136585671945225)
  ·
    refine ⟨118272544572852439253958919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157696726097136585671945225 118272544572852439253958919)
    ·
      refine ⟨177408816859278658880938379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118272544572852439253958919 177408816859278658880938379)
      ·
        refine ⟨266113225288917988321407569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177408816859278658880938379 266113225288917988321407569)
        ·
          refine ⟨199584918966688491241055677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266113225288917988321407569 199584918966688491241055677)
          ·
            refine ⟨74844344612508184215395879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199584918966688491241055677 74844344612508184215395879)
            ·
              refine ⟨112266516918762276323093819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74844344612508184215395879 112266516918762276323093819)
              ·
                refine ⟨168399775378143414484640729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112266516918762276323093819 168399775378143414484640729)
                ·
                  refine ⟨126299831533607560863480547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168399775378143414484640729 126299831533607560863480547)
                  ·
                    refine ⟨189449747300411341295220821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126299831533607560863480547 189449747300411341295220821)
                    ·
                      refine ⟨2220114226176695405803369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189449747300411341295220821 2220114226176695405803369)
                      ·
                        rfl

theorem cell23_4323657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_4323657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323657 prefixEnd_4323657 := by exact prefixLift 4323657
  have htrace : WordTrace (prefixWord ++ tailWord_4323657) baseStart_4323657 baseEnd_4323657 := by
    simpa [prefixWord, tailWord_4323657, baseEnd_4323657] using wordTrace_append hprefix tailTrace_4323657
  have hstable : (prefixWord ++ tailWord_4323657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323657).length < 2 ^ (prefixWord ++ tailWord_4323657).sum := by decide
  have hdescent : baseEnd_4323657 < baseStart_4323657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323664 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_4323664 : Nat := 118140960795 + 4323664 * 2 ^ 59
def prefixEnd_4323664 : Nat := 4983230072969 + 3 ^ 40 * 4323664 * 2
def baseEnd_4323664 : Nat := 2220117820541276878415837

theorem tailTrace_4323664 : CollatzResearch.WordTrace tailWord_4323664 prefixEnd_4323664 2220117820541276878415837 := by
  unfold tailWord_4323664
  simp only [CollatzResearch.WordTrace]
  refine ⟨78848490704055612933725023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105131320938740817244966697 78848490704055612933725023)
  ·
    refine ⟨118272736056083419400587535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78848490704055612933725023 118272736056083419400587535)
    ·
      refine ⟨177409104084125129100881303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118272736056083419400587535 177409104084125129100881303)
      ·
        refine ⟨266113656126187693651321955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177409104084125129100881303 266113656126187693651321955)
        ·
          refine ⟨399170484189281540476982933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266113656126187693651321955 399170484189281540476982933)
          ·
            refine ⟨18711116446372572209858575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 399170484189281540476982933 18711116446372572209858575)
            ·
              refine ⟨28066674669558858314787863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18711116446372572209858575 28066674669558858314787863)
              ·
                refine ⟨42100012004338287472181795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28066674669558858314787863 42100012004338287472181795)
                ·
                  refine ⟨63150018006507431208272693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42100012004338287472181795 63150018006507431208272693)
                  ·
                    refine ⟨5920314188110071675775565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63150018006507431208272693 5920314188110071675775565)
                    ·
                      refine ⟨2220117820541276878415837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5920314188110071675775565 2220117820541276878415837)
                      ·
                        rfl

theorem cell23_4323664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_4323664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323664 prefixEnd_4323664 := by exact prefixLift 4323664
  have htrace : WordTrace (prefixWord ++ tailWord_4323664) baseStart_4323664 baseEnd_4323664 := by
    simpa [prefixWord, tailWord_4323664, baseEnd_4323664] using wordTrace_append hprefix tailTrace_4323664
  have hstable : (prefixWord ++ tailWord_4323664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323664).length < 2 ^ (prefixWord ++ tailWord_4323664).sum := by decide
  have hdescent : baseEnd_4323664 < baseStart_4323664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323684 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_4323684 : Nat := 118140960795 + 4323684 * 2 ^ 59
def prefixEnd_4323684 : Nat := 4983230072969 + 3 ^ 40 * 4323684 * 2
def baseEnd_4323684 : Nat := 740042696718122266721915

theorem tailTrace_4323684 : CollatzResearch.WordTrace tailWord_4323684 prefixEnd_4323684 740042696718122266721915 := by
  unfold tailWord_4323684
  simp only [CollatzResearch.WordTrace]
  refine ⟨78848855434019384641589053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105131807245359179522118737 78848855434019384641589053)
  ·
    refine ⟨29568320787757269240595895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78848855434019384641589053 29568320787757269240595895)
    ·
      refine ⟨44352481181635903860893843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29568320787757269240595895 44352481181635903860893843)
      ·
        refine ⟨66528721772453855791340765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44352481181635903860893843 66528721772453855791340765)
        ·
          refine ⟨24948270664670195921752787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66528721772453855791340765 24948270664670195921752787)
          ·
            refine ⟨37422405997005293882629181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24948270664670195921752787 37422405997005293882629181)
            ·
              refine ⟨14033402248876985205985943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37422405997005293882629181 14033402248876985205985943)
              ·
                refine ⟨21050103373315477808978915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14033402248876985205985943 21050103373315477808978915)
                ·
                  refine ⟨31575155059973216713468373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21050103373315477808978915 31575155059973216713468373)
                  ·
                    refine ⟨740042696718122266721915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31575155059973216713468373 740042696718122266721915)
                    ·
                      rfl

theorem cell23_4323684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_4323684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323684 prefixEnd_4323684 := by exact prefixLift 4323684
  have htrace : WordTrace (prefixWord ++ tailWord_4323684) baseStart_4323684 baseEnd_4323684 := by
    simpa [prefixWord, tailWord_4323684, baseEnd_4323684] using wordTrace_append hprefix tailTrace_4323684
  have hstable : (prefixWord ++ tailWord_4323684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323684).length < 2 ^ (prefixWord ++ tailWord_4323684).sum := by decide
  have hdescent : baseEnd_4323684 < baseStart_4323684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323688 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 5]
def baseStart_4323688 : Nat := 118140960795 + 4323688 * 2 ^ 59
def prefixEnd_4323688 : Nat := 4983230072969 + 3 ^ 40 * 4323688 * 2
def baseEnd_4323688 : Nat := 246681127119664976057303

theorem tailTrace_4323688 : CollatzResearch.WordTrace tailWord_4323688 prefixEnd_4323688 246681127119664976057303 := by
  unfold tailWord_4323688
  simp only [CollatzResearch.WordTrace]
  refine ⟨78848928380012138983161859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105131904506682851977549145 78848928380012138983161859)
  ·
    refine ⟨118273392570018208474742789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78848928380012138983161859 118273392570018208474742789)
    ·
      refine ⟨22176261106878414089014273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118273392570018208474742789 22176261106878414089014273)
      ·
        refine ⟨16632195830158810566760705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22176261106878414089014273 16632195830158810566760705)
        ·
          refine ⟨12474146872619107925070529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16632195830158810566760705 12474146872619107925070529)
          ·
            refine ⟨9355610154464330943802897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12474146872619107925070529 9355610154464330943802897)
            ·
              refine ⟨7016707615848248207852173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9355610154464330943802897 7016707615848248207852173)
              ·
                refine ⟨2631265355943093077944565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7016707615848248207852173 2631265355943093077944565)
                ·
                  refine ⟨246681127119664976057303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2631265355943093077944565 246681127119664976057303)
                  ·
                    rfl

theorem cell23_4323688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 5].length) (baseStart_4323688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323688 prefixEnd_4323688 := by exact prefixLift 4323688
  have htrace : WordTrace (prefixWord ++ tailWord_4323688) baseStart_4323688 baseEnd_4323688 := by
    simpa [prefixWord, tailWord_4323688, baseEnd_4323688] using wordTrace_append hprefix tailTrace_4323688
  have hstable : (prefixWord ++ tailWord_4323688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323688).length < 2 ^ (prefixWord ++ tailWord_4323688).sum := by decide
  have hdescent : baseEnd_4323688 < baseStart_4323688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323744 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 8]
def baseStart_4323744 : Nat := 118140960795 + 4323744 * 2 ^ 59
def prefixEnd_4323744 : Nat := 4983230072969 + 3 ^ 40 * 4323744 * 2
def baseEnd_4323744 : Nat := 246684322110404062823941

theorem tailTrace_4323744 : CollatzResearch.WordTrace tailWord_4323744 prefixEnd_4323744 246684322110404062823941 := by
  unfold tailWord_4323744
  simp only [CollatzResearch.WordTrace]
  refine ⟨78849949623910699765181143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105133266165214266353574857 78849949623910699765181143)
  ·
    refine ⟨118274924435866049647771715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78849949623910699765181143 118274924435866049647771715)
    ·
      refine ⟨177412386653799074471657573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118274924435866049647771715 177412386653799074471657573)
      ·
        refine ⟨33264822497587326463435795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177412386653799074471657573 33264822497587326463435795)
        ·
          refine ⟨49897233746380989695153693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33264822497587326463435795 49897233746380989695153693)
          ·
            refine ⟨18711462654892871135682635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49897233746380989695153693 18711462654892871135682635)
            ·
              refine ⟨28067193982339306703523953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18711462654892871135682635 28067193982339306703523953)
              ·
                refine ⟨21050395486754480027642965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28067193982339306703523953 21050395486754480027642965)
                ·
                  refine ⟨246684322110404062823941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21050395486754480027642965 246684322110404062823941)
                  ·
                    rfl

theorem cell23_4323744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_4323744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323744 prefixEnd_4323744 := by exact prefixLift 4323744
  have htrace : WordTrace (prefixWord ++ tailWord_4323744) baseStart_4323744 baseEnd_4323744 := by
    simpa [prefixWord, tailWord_4323744, baseEnd_4323744] using wordTrace_append hprefix tailTrace_4323744
  have hstable : (prefixWord ++ tailWord_4323744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323744).length < 2 ^ (prefixWord ++ tailWord_4323744).sum := by decide
  have hdescent : baseEnd_4323744 < baseStart_4323744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323765 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4323765 : Nat := 118140960795 + 4323765 * 2 ^ 59
def prefixEnd_4323765 : Nat := 4983230072969 + 3 ^ 40 * 4323765 * 2
def baseEnd_4323765 : Nat := 740056560695793661084291

theorem tailTrace_4323765 : CollatzResearch.WordTrace tailWord_4323765 prefixEnd_4323765 740056560695793661084291 := by
  unfold tailWord_4323765
  simp only [CollatzResearch.WordTrace]
  refine ⟨157700665180745320116876749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105133776787163546744584499 157700665180745320116876749)
  ·
    refine ⟨59137749442779495043828781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157700665180745320116876749 59137749442779495043828781)
    ·
      refine ⟨22176656041042310641435793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59137749442779495043828781 22176656041042310641435793)
      ·
        refine ⟨16632492030781732981076845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22176656041042310641435793 16632492030781732981076845)
        ·
          refine ⟨6237184511543149867903817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16632492030781732981076845 6237184511543149867903817)
          ·
            refine ⟨4677888383657362400927863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237184511543149867903817 4677888383657362400927863)
            ·
              refine ⟨7016832575486043601391795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4677888383657362400927863 7016832575486043601391795)
              ·
                refine ⟨10525248863229065402087693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7016832575486043601391795 10525248863229065402087693)
                ·
                  refine ⟨3946968323710899525782885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10525248863229065402087693 3946968323710899525782885)
                  ·
                    refine ⟨740056560695793661084291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3946968323710899525782885 740056560695793661084291)
                    ·
                      rfl

theorem cell23_4323765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4323765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323765 prefixEnd_4323765 := by exact prefixLift 4323765
  have htrace : WordTrace (prefixWord ++ tailWord_4323765) baseStart_4323765 baseEnd_4323765 := by
    simpa [prefixWord, tailWord_4323765, baseEnd_4323765] using wordTrace_append hprefix tailTrace_4323765
  have hstable : (prefixWord ++ tailWord_4323765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323765).length < 2 ^ (prefixWord ++ tailWord_4323765).sum := by decide
  have hdescent : baseEnd_4323765 < baseStart_4323765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323771 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 3]
def baseStart_4323771 : Nat := 118140960795 + 4323771 * 2 ^ 59
def prefixEnd_4323771 : Nat := 4983230072969 + 3 ^ 40 * 4323771 * 2
def baseEnd_4323771 : Nat := 2220172762971307959777845

theorem tailTrace_4323771 : CollatzResearch.WordTrace tailWord_4323771 prefixEnd_4323771 2220172762971307959777845 := by
  unfold tailWord_4323771
  simp only [CollatzResearch.WordTrace]
  refine ⟨157700884018723583141595167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105133922679149055427730111 157700884018723583141595167)
  ·
    refine ⟨236551326028085374712392751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157700884018723583141595167 236551326028085374712392751)
    ·
      refine ⟨354826989042128062068589127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236551326028085374712392751 354826989042128062068589127)
      ·
        refine ⟨532240483563192093102883691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354826989042128062068589127 532240483563192093102883691)
        ·
          refine ⟨798360725344788139654325537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532240483563192093102883691 798360725344788139654325537)
          ·
            refine ⟨598770544008591104740744153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798360725344788139654325537 598770544008591104740744153)
            ·
              refine ⟨449077908006443328555558115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598770544008591104740744153 449077908006443328555558115)
              ·
                refine ⟨673616862009664992833337173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449077908006443328555558115 673616862009664992833337173)
                ·
                  refine ⟨3946973800837880817382835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 673616862009664992833337173 3946973800837880817382835)
                  ·
                    refine ⟨5920460701256821226074253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3946973800837880817382835 5920460701256821226074253)
                    ·
                      refine ⟨2220172762971307959777845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5920460701256821226074253 2220172762971307959777845)
                      ·
                        rfl

theorem cell23_4323771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 9, 1, 3].length) (baseStart_4323771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323771 prefixEnd_4323771 := by exact prefixLift 4323771
  have htrace : WordTrace (prefixWord ++ tailWord_4323771) baseStart_4323771 baseEnd_4323771 := by
    simpa [prefixWord, tailWord_4323771, baseEnd_4323771] using wordTrace_append hprefix tailTrace_4323771
  have hstable : (prefixWord ++ tailWord_4323771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323771).length < 2 ^ (prefixWord ++ tailWord_4323771).sum := by decide
  have hdescent : baseEnd_4323771 < baseStart_4323771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323808 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 1, 5]
def baseStart_4323808 : Nat := 118140960795 + 4323808 * 2 ^ 59
def prefixEnd_4323808 : Nat := 4983230072969 + 3 ^ 40 * 4323808 * 2
def baseEnd_4323808 : Nat := 740063920585174771671725

theorem tailTrace_4323808 : CollatzResearch.WordTrace tailWord_4323808 prefixEnd_4323808 740063920585174771671725 := by
  unfold tailWord_4323808
  simp only [CollatzResearch.WordTrace]
  refine ⟨78851116759794769230346039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105134822346393025640461385 78851116759794769230346039)
  ·
    refine ⟨118276675139692153845519059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78851116759794769230346039 118276675139692153845519059)
    ·
      refine ⟨177415012709538230768278589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118276675139692153845519059 177415012709538230768278589)
      ·
        refine ⟨66530629766076836538104471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177415012709538230768278589 66530629766076836538104471)
        ·
          refine ⟨99795944649115254807156707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66530629766076836538104471 99795944649115254807156707)
          ·
            refine ⟨149693916973672882210735061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99795944649115254807156707 149693916973672882210735061)
            ·
              refine ⟨3508451179070458176814103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 149693916973672882210735061 3508451179070458176814103)
              ·
                refine ⟨5262676768605687265221155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508451179070458176814103 5262676768605687265221155)
                ·
                  refine ⟨7894015152908530897831733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5262676768605687265221155 7894015152908530897831733)
                  ·
                    refine ⟨740063920585174771671725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7894015152908530897831733 740063920585174771671725)
                    ·
                      rfl

theorem cell23_4323808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 5].length) (baseStart_4323808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323808 prefixEnd_4323808 := by exact prefixLift 4323808
  have htrace : WordTrace (prefixWord ++ tailWord_4323808) baseStart_4323808 baseEnd_4323808 := by
    simpa [prefixWord, tailWord_4323808, baseEnd_4323808] using wordTrace_append hprefix tailTrace_4323808
  have hstable : (prefixWord ++ tailWord_4323808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323808).length < 2 ^ (prefixWord ++ tailWord_4323808).sum := by decide
  have hdescent : baseEnd_4323808 < baseStart_4323808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323822 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_4323822 : Nat := 118140960795 + 4323822 * 2 ^ 59
def prefixEnd_4323822 : Nat := 4983230072969 + 3 ^ 40 * 4323822 * 2
def baseEnd_4323822 : Nat := 2220198950484687260240111

theorem tailTrace_4323822 : CollatzResearch.WordTrace tailWord_4323822 prefixEnd_4323822 2220198950484687260240111 := by
  unfold tailWord_4323822
  simp only [CollatzResearch.WordTrace]
  refine ⟨19712843017692352356462715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105135162761025879234467813 19712843017692352356462715)
  ·
    refine ⟨29569264526538528534694073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19712843017692352356462715 29569264526538528534694073)
    ·
      refine ⟨22176948394903896401020555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29569264526538528534694073 22176948394903896401020555)
      ·
        refine ⟨33265422592355844601530833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22176948394903896401020555 33265422592355844601530833)
        ·
          refine ⟨24949066944266883451148125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33265422592355844601530833 24949066944266883451148125)
          ·
            refine ⟨9355900104100081294180547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24949066944266883451148125 9355900104100081294180547)
            ·
              refine ⟨14033850156150121941270821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9355900104100081294180547 14033850156150121941270821)
              ·
                refine ⟨2631346904278147863988279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14033850156150121941270821 2631346904278147863988279)
                ·
                  refine ⟨3947020356417221795982419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631346904278147863988279 3947020356417221795982419)
                  ·
                    refine ⟨5920530534625832693973629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947020356417221795982419 5920530534625832693973629)
                    ·
                      refine ⟨2220198950484687260240111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5920530534625832693973629 2220198950484687260240111)
                      ·
                        rfl

theorem cell23_4323822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_4323822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323822 prefixEnd_4323822 := by exact prefixLift 4323822
  have htrace : WordTrace (prefixWord ++ tailWord_4323822) baseStart_4323822 baseEnd_4323822 := by
    simpa [prefixWord, tailWord_4323822, baseEnd_4323822] using wordTrace_append hprefix tailTrace_4323822
  have hstable : (prefixWord ++ tailWord_4323822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323822).length < 2 ^ (prefixWord ++ tailWord_4323822).sum := by decide
  have hdescent : baseEnd_4323822 < baseStart_4323822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323834 : List Nat := [3, 1, 1, 1, 1, 2, 2, 12]
def baseStart_4323834 : Nat := 118140960795 + 4323834 * 2 ^ 59
def prefixEnd_4323834 : Nat := 4983230072969 + 3 ^ 40 * 4323834 * 2
def baseEnd_4323834 : Nat := 82229818972316341232965

theorem tailTrace_4323834 : CollatzResearch.WordTrace tailWord_4323834 prefixEnd_4323834 82229818972316341232965 := by
  unfold tailWord_4323834
  simp only [CollatzResearch.WordTrace]
  refine ⟨39425795454373836225284639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105135454544996896600759037 39425795454373836225284639)
  ·
    refine ⟨59138693181560754337926959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39425795454373836225284639 59138693181560754337926959)
    ·
      refine ⟨88708039772341131506890439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59138693181560754337926959 88708039772341131506890439)
      ·
        refine ⟨133062059658511697260335659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88708039772341131506890439 133062059658511697260335659)
        ·
          refine ⟨199593089487767545890503489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133062059658511697260335659 199593089487767545890503489)
          ·
            refine ⟨149694817115825659417877617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199593089487767545890503489 149694817115825659417877617)
            ·
              refine ⟨112271112836869244563408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149694817115825659417877617 112271112836869244563408213)
              ·
                refine ⟨82229818972316341232965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 112271112836869244563408213 82229818972316341232965)
                ·
                  rfl

theorem cell23_4323834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_4323834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323834 prefixEnd_4323834 := by exact prefixLift 4323834
  have htrace : WordTrace (prefixWord ++ tailWord_4323834) baseStart_4323834 baseEnd_4323834 := by
    simpa [prefixWord, tailWord_4323834, baseEnd_4323834] using wordTrace_append hprefix tailTrace_4323834
  have hstable : (prefixWord ++ tailWord_4323834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323834).length < 2 ^ (prefixWord ++ tailWord_4323834).sum := by decide
  have hdescent : baseEnd_4323834 < baseStart_4323834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323848 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_4323848 : Nat := 118140960795 + 4323848 * 2 ^ 59
def prefixEnd_4323848 : Nat := 4983230072969 + 3 ^ 40 * 4323848 * 2
def baseEnd_4323848 : Nat := 2220212300981704158514991

theorem tailTrace_4323848 : CollatzResearch.WordTrace tailWord_4323848 prefixEnd_4323848 2220212300981704158514991 := by
  unfold tailWord_4323848
  simp only [CollatzResearch.WordTrace]
  refine ⟨78851846219722312646074099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105135794959629750194765465 78851846219722312646074099)
  ·
    refine ⟨118277769329583468969111149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78851846219722312646074099 118277769329583468969111149)
    ·
      refine ⟨44354163498593800863416681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118277769329583468969111149 44354163498593800863416681)
      ·
        refine ⟨33265622623945350647562511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44354163498593800863416681 33265622623945350647562511)
        ·
          refine ⟨49898433935918025971343767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33265622623945350647562511 49898433935918025971343767)
          ·
            refine ⟨74847650903877038957015651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49898433935918025971343767 74847650903877038957015651)
            ·
              refine ⟨112271476355815558435523477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74847650903877038957015651 112271476355815558435523477)
              ·
                refine ⟨5262725454178854301665163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112271476355815558435523477 5262725454178854301665163)
                ·
                  refine ⟨7894088181268281452497745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5262725454178854301665163 7894088181268281452497745)
                  ·
                    refine ⟨5920566135951211089373309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7894088181268281452497745 5920566135951211089373309)
                    ·
                      refine ⟨2220212300981704158514991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5920566135951211089373309 2220212300981704158514991)
                      ·
                        rfl

theorem cell23_4323848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_4323848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323848 prefixEnd_4323848 := by exact prefixLift 4323848
  have htrace : WordTrace (prefixWord ++ tailWord_4323848) baseStart_4323848 baseEnd_4323848 := by
    simpa [prefixWord, tailWord_4323848, baseEnd_4323848] using wordTrace_append hprefix tailTrace_4323848
  have hstable : (prefixWord ++ tailWord_4323848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323848).length < 2 ^ (prefixWord ++ tailWord_4323848).sum := by decide
  have hdescent : baseEnd_4323848 < baseStart_4323848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323872 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 2, 4]
def baseStart_4323872 : Nat := 118140960795 + 4323872 * 2 ^ 59
def prefixEnd_4323872 : Nat := 4983230072969 + 3 ^ 40 * 4323872 * 2
def baseEnd_4323872 : Nat := 740074874839137354871627

theorem tailTrace_4323872 : CollatzResearch.WordTrace tailWord_4323872 prefixEnd_4323872 740074874839137354871627 := by
  unfold tailWord_4323872
  simp only [CollatzResearch.WordTrace]
  refine ⟨78852283895678838695510935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105136378527571784927347913 78852283895678838695510935)
  ·
    refine ⟨118278425843518258043266403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78852283895678838695510935 118278425843518258043266403)
    ·
      refine ⟨177417638765277387064899605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118278425843518258043266403 177417638765277387064899605)
      ·
        refine ⟨8316451817122377518667169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177417638765277387064899605 8316451817122377518667169)
        ·
          refine ⟨6237338862841783139000377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8316451817122377518667169 6237338862841783139000377)
          ·
            refine ⟨4678004147131337354250283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237338862841783139000377 4678004147131337354250283)
            ·
              refine ⟨7017006220697006031375425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678004147131337354250283 7017006220697006031375425)
              ·
                refine ⟨5262754665522754523531569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7017006220697006031375425 5262754665522754523531569)
                ·
                  refine ⟨3947065999142065892648677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5262754665522754523531569 3947065999142065892648677)
                  ·
                    refine ⟨740074874839137354871627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3947065999142065892648677 740074874839137354871627)
                    ·
                      rfl

theorem cell23_4323872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_4323872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323872 prefixEnd_4323872 := by exact prefixLift 4323872
  have htrace : WordTrace (prefixWord ++ tailWord_4323872) baseStart_4323872 baseEnd_4323872 := by
    simpa [prefixWord, tailWord_4323872, baseEnd_4323872] using wordTrace_append hprefix tailTrace_4323872
  have hstable : (prefixWord ++ tailWord_4323872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323872).length < 2 ^ (prefixWord ++ tailWord_4323872).sum := by decide
  have hdescent : baseEnd_4323872 < baseStart_4323872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323888 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 5, 3, 2]
def baseStart_4323888 : Nat := 118140960795 + 4323888 * 2 ^ 59
def prefixEnd_4323888 : Nat := 4983230072969 + 3 ^ 40 * 4323888 * 2
def baseEnd_4323888 : Nat := 2220232840207884002014807

theorem tailTrace_4323888 : CollatzResearch.WordTrace tailWord_4323888 prefixEnd_4323888 2220232840207884002014807 := by
  unfold tailWord_4323888
  simp only [CollatzResearch.WordTrace]
  refine ⟨78852575679649856061802159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105136767572866474749069545 78852575679649856061802159)
  ·
    refine ⟨118278863519474784092703239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78852575679649856061802159 118278863519474784092703239)
    ·
      refine ⟨177418295279212176139054859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118278863519474784092703239 177418295279212176139054859)
      ·
        refine ⟨266127442918818264208582289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177418295279212176139054859 266127442918818264208582289)
        ·
          refine ⟨199595582189113698156436717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266127442918818264208582289 199595582189113698156436717)
          ·
            refine ⟨74848343320917636808663769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199595582189113698156436717 74848343320917636808663769)
            ·
              refine ⟨56136257490688227606497827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74848343320917636808663769 56136257490688227606497827)
              ·
                refine ⟨84204386236032341409746741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56136257490688227606497827 84204386236032341409746741)
                ·
                  refine ⟨7894161209628032007163757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84204386236032341409746741 7894161209628032007163757)
                  ·
                    refine ⟨2960310453610512002686409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7894161209628032007163757 2960310453610512002686409)
                    ·
                      refine ⟨2220232840207884002014807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960310453610512002686409 2220232840207884002014807)
                      ·
                        rfl

theorem cell23_4323888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 3, 2].length) (baseStart_4323888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323888 prefixEnd_4323888 := by exact prefixLift 4323888
  have htrace : WordTrace (prefixWord ++ tailWord_4323888) baseStart_4323888 baseEnd_4323888 := by
    simpa [prefixWord, tailWord_4323888, baseEnd_4323888] using wordTrace_append hprefix tailTrace_4323888
  have hstable : (prefixWord ++ tailWord_4323888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323888).length < 2 ^ (prefixWord ++ tailWord_4323888).sum := by decide
  have hdescent : baseEnd_4323888 < baseStart_4323888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323902 : List Nat := [4, 2, 1, 4, 1, 2, 2, 7]
def baseStart_4323902 : Nat := 118140960795 + 4323902 * 2 ^ 59
def prefixEnd_4323902 : Nat := 4983230072969 + 3 ^ 40 * 4323902 * 2
def baseEnd_4323902 : Nat := 82231112182853590638509

theorem tailTrace_4323902 : CollatzResearch.WordTrace tailWord_4323902 prefixEnd_4323902 82231112182853590638509 := by
  unfold tailWord_4323902
  simp only [CollatzResearch.WordTrace]
  refine ⟨19713207747656124064326745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105137107987499328343075973 19713207747656124064326745)
  ·
    refine ⟨14784905810742093048245059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19713207747656124064326745 14784905810742093048245059)
    ·
      refine ⟨22177358716113139572367589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14784905810742093048245059 22177358716113139572367589)
      ·
        refine ⟨4158254759271213669818923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22177358716113139572367589 4158254759271213669818923)
        ·
          refine ⟨6237382138906820504728385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158254759271213669818923 6237382138906820504728385)
          ·
            refine ⟨4678036604180115378546289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237382138906820504728385 4678036604180115378546289)
            ·
              refine ⟨3508527453135086533909717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4678036604180115378546289 3508527453135086533909717)
              ·
                refine ⟨82231112182853590638509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3508527453135086533909717 82231112182853590638509)
                ·
                  rfl

theorem cell23_4323902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_4323902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323902 prefixEnd_4323902 := by exact prefixLift 4323902
  have htrace : WordTrace (prefixWord ++ tailWord_4323902) baseStart_4323902 baseEnd_4323902 := by
    simpa [prefixWord, tailWord_4323902, baseEnd_4323902] using wordTrace_append hprefix tailTrace_4323902
  have hstable : (prefixWord ++ tailWord_4323902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323902).length < 2 ^ (prefixWord ++ tailWord_4323902).sum := by decide
  have hdescent : baseEnd_4323902 < baseStart_4323902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323921 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_4323921 : Nat := 118140960795 + 4323921 * 2 ^ 59
def prefixEnd_4323921 : Nat := 4983230072969 + 3 ^ 40 * 4323921 * 2
def baseEnd_4323921 : Nat := 2220249785069482372902155

theorem tailTrace_4323921 : CollatzResearch.WordTrace tailWord_4323921 prefixEnd_4323921 2220249785069482372902155 := by
  unfold tailWord_4323921
  simp only [CollatzResearch.WordTrace]
  refine ⟨157706354968180158759555617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105137569978786772506370411 157706354968180158759555617)
  ·
    refine ⟨118279766226135119069666713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157706354968180158759555617 118279766226135119069666713)
    ·
      refine ⟨88709824669601339302250035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118279766226135119069666713 88709824669601339302250035)
      ·
        refine ⟨133064737004402008953375053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88709824669601339302250035 133064737004402008953375053)
        ·
          refine ⟨49899276376650753357515645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133064737004402008953375053 49899276376650753357515645)
          ·
            refine ⟨18712228641244032509068367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49899276376650753357515645 18712228641244032509068367)
            ·
              refine ⟨28068342961866048763602551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18712228641244032509068367 28068342961866048763602551)
              ·
                refine ⟨42102514442799073145403827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28068342961866048763602551 42102514442799073145403827)
                ·
                  refine ⟨63153771664198609718105741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42102514442799073145403827 63153771664198609718105741)
                  ·
                    refine ⟨23682664374074478644289653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63153771664198609718105741 23682664374074478644289653)
                    ·
                      refine ⟨2220249785069482372902155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23682664374074478644289653 2220249785069482372902155)
                      ·
                        rfl

theorem cell23_4323921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_4323921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323921 prefixEnd_4323921 := by exact prefixLift 4323921
  have htrace : WordTrace (prefixWord ++ tailWord_4323921) baseStart_4323921 baseEnd_4323921 := by
    simpa [prefixWord, tailWord_4323921, baseEnd_4323921] using wordTrace_append hprefix tailTrace_4323921
  have hstable : (prefixWord ++ tailWord_4323921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323921).length < 2 ^ (prefixWord ++ tailWord_4323921).sum := by decide
  have hdescent : baseEnd_4323921 < baseStart_4323921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4323971 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 1, 7]
def baseStart_4323971 : Nat := 118140960795 + 4323971 * 2 ^ 59
def prefixEnd_4323971 : Nat := 4983230072969 + 3 ^ 40 * 4323971 * 2
def baseEnd_4323971 : Nat := 740091819700735725758975

theorem tailTrace_4323971 : CollatzResearch.WordTrace tailWord_4323971 prefixEnd_4323971 740091819700735725758975 := by
  unfold tailWord_4323971
  simp only [CollatzResearch.WordTrace]
  refine ⟨157708178617999017298875767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105138785745332678199250511 157708178617999017298875767)
  ·
    refine ⟨236562267926998525948313651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157708178617999017298875767 236562267926998525948313651)
    ·
      refine ⟨354843401890497788922470477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236562267926998525948313651 354843401890497788922470477)
      ·
        refine ⟨133066275708936670845926429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354843401890497788922470477 133066275708936670845926429)
        ·
          refine ⟨49899853390851251567222411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133066275708936670845926429 49899853390851251567222411)
          ·
            refine ⟨74849780086276877350833617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49899853390851251567222411 74849780086276877350833617)
            ·
              refine ⟨56137335064707658013125213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74849780086276877350833617 56137335064707658013125213)
              ·
                refine ⟨21051500649265371754921955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56137335064707658013125213 21051500649265371754921955)
                ·
                  refine ⟨31577250973898057632382933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21051500649265371754921955 31577250973898057632382933)
                  ·
                    refine ⟨740091819700735725758975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31577250973898057632382933 740091819700735725758975)
                    ·
                      rfl

theorem cell23_4323971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 7].length) (baseStart_4323971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4323971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4323971 prefixEnd_4323971 := by exact prefixLift 4323971
  have htrace : WordTrace (prefixWord ++ tailWord_4323971) baseStart_4323971 baseEnd_4323971 := by
    simpa [prefixWord, tailWord_4323971, baseEnd_4323971] using wordTrace_append hprefix tailTrace_4323971
  have hstable : (prefixWord ++ tailWord_4323971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4323971).length < 2 ^ (prefixWord ++ tailWord_4323971).sum := by decide
  have hdescent : baseEnd_4323971 < baseStart_4323971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4323971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324022 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4324022 : Nat := 118140960795 + 4324022 * 2 ^ 59
def prefixEnd_4324022 : Nat := 4983230072969 + 3 ^ 40 * 4324022 * 2
def baseEnd_4324022 : Nat := 740100548871862159246397

theorem tailTrace_4324022 : CollatzResearch.WordTrace tailWord_4324022 prefixEnd_4324022 740100548871862159246397 := by
  unfold tailWord_4324022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9856877421300890813061395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105140025827209502005988213 9856877421300890813061395)
  ·
    refine ⟨14785316131951336219592093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9856877421300890813061395 14785316131951336219592093)
    ·
      refine ⟨5544493549481751082347035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14785316131951336219592093 5544493549481751082347035)
      ·
        refine ⟨8316740324222626623520553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5544493549481751082347035 8316740324222626623520553)
        ·
          refine ⟨6237555243166969967640415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8316740324222626623520553 6237555243166969967640415)
          ·
            refine ⟨9356332864750454951460623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237555243166969967640415 9356332864750454951460623)
            ·
              refine ⟨14034499297125682427190935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9356332864750454951460623 14034499297125682427190935)
              ·
                refine ⟨21051748945688523640786403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14034499297125682427190935 21051748945688523640786403)
                ·
                  refine ⟨31577623418532785461179605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21051748945688523640786403 31577623418532785461179605)
                  ·
                    refine ⟨740100548871862159246397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31577623418532785461179605 740100548871862159246397)
                    ·
                      rfl

theorem cell23_4324022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4324022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324022 prefixEnd_4324022 := by exact prefixLift 4324022
  have htrace : WordTrace (prefixWord ++ tailWord_4324022) baseStart_4324022 baseEnd_4324022 := by
    simpa [prefixWord, tailWord_4324022, baseEnd_4324022] using wordTrace_append hprefix tailTrace_4324022
  have hstable : (prefixWord ++ tailWord_4324022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324022).length < 2 ^ (prefixWord ++ tailWord_4324022).sum := by decide
  have hdescent : baseEnd_4324022 < baseStart_4324022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324041 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_4324041 : Nat := 118140960795 + 4324041 * 2 ^ 59
def prefixEnd_4324041 : Nat := 4983230072969 + 3 ^ 40 * 4324041 * 2
def baseEnd_4324041 : Nat := 2220311402748021903401603

theorem tailTrace_4324041 : CollatzResearch.WordTrace tailWord_4324041 prefixEnd_4324041 2220311402748021903401603 := by
  unfold tailWord_4324041
  simp only [CollatzResearch.WordTrace]
  refine ⟨157710731727745419253923977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105140487818496946169282651 157710731727745419253923977)
  ·
    refine ⟨118283048795809064440442983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157710731727745419253923977 118283048795809064440442983)
    ·
      refine ⟨177424573193713596660664475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118283048795809064440442983 177424573193713596660664475)
      ·
        refine ⟨266136859790570394990996713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177424573193713596660664475 266136859790570394990996713)
        ·
          refine ⟨199602644842927796243247535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266136859790570394990996713 199602644842927796243247535)
          ·
            refine ⟨299403967264391694364871303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199602644842927796243247535 299403967264391694364871303)
            ·
              refine ⟨449105950896587541547306955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299403967264391694364871303 449105950896587541547306955)
              ·
                refine ⟨673658926344881312320960433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449105950896587541547306955 673658926344881312320960433)
                ·
                  refine ⟨505244194758660984240720325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673658926344881312320960433 505244194758660984240720325)
                  ·
                    refine ⟨94733286517248934545135061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 505244194758660984240720325 94733286517248934545135061)
                    ·
                      refine ⟨2220311402748021903401603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94733286517248934545135061 2220311402748021903401603)
                      ·
                        rfl

theorem cell23_4324041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_4324041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324041 prefixEnd_4324041 := by exact prefixLift 4324041
  have htrace : WordTrace (prefixWord ++ tailWord_4324041) baseStart_4324041 baseEnd_4324041 := by
    simpa [prefixWord, tailWord_4324041, baseEnd_4324041] using wordTrace_append hprefix tailTrace_4324041
  have hstable : (prefixWord ++ tailWord_4324041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324041).length < 2 ^ (prefixWord ++ tailWord_4324041).sum := by decide
  have hdescent : baseEnd_4324041 < baseStart_4324041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324132 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_4324132 : Nat := 118140960795 + 4324132 * 2 ^ 59
def prefixEnd_4324132 : Nat := 4983230072969 + 3 ^ 40 * 4324132 * 2
def baseEnd_4324132 : Nat := 2220358129487581047363685

theorem tailTrace_4324132 : CollatzResearch.WordTrace tailWord_4324132 prefixEnd_4324132 2220358129487581047363685 := by
  unfold tailWord_4324132
  simp only [CollatzResearch.WordTrace]
  refine ⟨78857025385207870897743325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105142700513610494530324433 78857025385207870897743325)
  ·
    refine ⟨29571384519452951586653747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78857025385207870897743325 29571384519452951586653747)
    ·
      refine ⟨44357076779179427379980621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29571384519452951586653747 44357076779179427379980621)
      ·
        refine ⟨16633903792192285267492733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44357076779179427379980621 16633903792192285267492733)
        ·
          refine ⟨6237713922072106975309775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16633903792192285267492733 6237713922072106975309775)
          ·
            refine ⟨9356570883108160462964663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237713922072106975309775 9356570883108160462964663)
            ·
              refine ⟨14034856324662240694446995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9356570883108160462964663 14034856324662240694446995)
              ·
                refine ⟨21052284486993361041670493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14034856324662240694446995 21052284486993361041670493)
                ·
                  refine ⟨7894606682622510390626435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21052284486993361041670493 7894606682622510390626435)
                  ·
                    refine ⟨11841910023933765585939653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7894606682622510390626435 11841910023933765585939653)
                    ·
                      refine ⟨2220358129487581047363685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11841910023933765585939653 2220358129487581047363685)
                      ·
                        rfl

theorem cell23_4324132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_4324132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324132 prefixEnd_4324132 := by exact prefixLift 4324132
  have htrace : WordTrace (prefixWord ++ tailWord_4324132) baseStart_4324132 baseEnd_4324132 := by
    simpa [prefixWord, tailWord_4324132, baseEnd_4324132] using wordTrace_append hprefix tailTrace_4324132
  have hstable : (prefixWord ++ tailWord_4324132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324132).length < 2 ^ (prefixWord ++ tailWord_4324132).sum := by decide
  have hdescent : baseEnd_4324132 < baseStart_4324132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324142 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_4324142 : Nat := 118140960795 + 4324142 * 2 ^ 59
def prefixEnd_4324142 : Nat := 4983230072969 + 3 ^ 40 * 4324142 * 2
def baseEnd_4324142 : Nat := 740121088098042002746213

theorem tailTrace_4324142 : CollatzResearch.WordTrace tailWord_4324142 prefixEnd_4324142 740121088098042002746213 := by
  unfold tailWord_4324142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19714301937547439187918835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105142943666919675668900453 19714301937547439187918835)
  ·
    refine ⟨29571452906321158781878253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19714301937547439187918835 29571452906321158781878253)
    ·
      refine ⟨11089294839870434543204345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29571452906321158781878253 11089294839870434543204345)
      ·
        refine ⟨8316971129902825907403259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11089294839870434543204345 8316971129902825907403259)
        ·
          refine ⟨12475456694854238861104889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8316971129902825907403259 12475456694854238861104889)
          ·
            refine ⟨9356592521140679145828667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12475456694854238861104889 9356592521140679145828667)
            ·
              refine ⟨14034888781711018718743001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9356592521140679145828667 14034888781711018718743001)
              ·
                refine ⟨10526166586283264039057251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14034888781711018718743001 10526166586283264039057251)
                ·
                  refine ⟨15789249879424896058585877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10526166586283264039057251 15789249879424896058585877)
                  ·
                    refine ⟨740121088098042002746213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15789249879424896058585877 740121088098042002746213)
                    ·
                      rfl

theorem cell23_4324142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_4324142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324142 prefixEnd_4324142 := by exact prefixLift 4324142
  have htrace : WordTrace (prefixWord ++ tailWord_4324142) baseStart_4324142 baseEnd_4324142 := by
    simpa [prefixWord, tailWord_4324142, baseEnd_4324142] using wordTrace_append hprefix tailTrace_4324142
  have hstable : (prefixWord ++ tailWord_4324142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324142).length < 2 ^ (prefixWord ++ tailWord_4324142).sum := by decide
  have hdescent : baseEnd_4324142 < baseStart_4324142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324145 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_4324145 : Nat := 118140960795 + 4324145 * 2 ^ 59
def prefixEnd_4324145 : Nat := 4983230072969 + 3 ^ 40 * 4324145 * 2
def baseEnd_4324145 : Nat := 2220364804736089496501125

theorem tailTrace_4324145 : CollatzResearch.WordTrace tailWord_4324145 prefixEnd_4324145 2220364804736089496501125 := by
  unfold tailWord_4324145
  simp only [CollatzResearch.WordTrace]
  refine ⟨157714524919368645015709889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105143016612912430010473259 157714524919368645015709889)
  ·
    refine ⟨118285893689526483761782417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157714524919368645015709889 118285893689526483761782417)
    ·
      refine ⟨88714420267144862821336813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118285893689526483761782417 88714420267144862821336813)
      ·
        refine ⟨33267907600179323558001305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88714420267144862821336813 33267907600179323558001305)
        ·
          refine ⟨24950930700134492668500979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33267907600179323558001305 24950930700134492668500979)
          ·
            refine ⟨37426396050201739002751469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24950930700134492668500979 37426396050201739002751469)
            ·
              refine ⟨14034898518825652126031801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37426396050201739002751469 14034898518825652126031801)
              ·
                refine ⟨10526173889119239094523851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14034898518825652126031801 10526173889119239094523851)
                ·
                  refine ⟨15789260833678858641785777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10526173889119239094523851 15789260833678858641785777)
                  ·
                    refine ⟨11841945625259143981339333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15789260833678858641785777 11841945625259143981339333)
                    ·
                      refine ⟨2220364804736089496501125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11841945625259143981339333 2220364804736089496501125)
                      ·
                        rfl

theorem cell23_4324145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_4324145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324145 prefixEnd_4324145 := by exact prefixLift 4324145
  have htrace : WordTrace (prefixWord ++ tailWord_4324145) baseStart_4324145 baseEnd_4324145 := by
    simpa [prefixWord, tailWord_4324145, baseEnd_4324145] using wordTrace_append hprefix tailTrace_4324145
  have hstable : (prefixWord ++ tailWord_4324145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324145).length < 2 ^ (prefixWord ++ tailWord_4324145).sum := by decide
  have hdescent : baseEnd_4324145 < baseStart_4324145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324149 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_4324149 : Nat := 118140960795 + 4324149 * 2 ^ 59
def prefixEnd_4324149 : Nat := 4983230072969 + 3 ^ 40 * 4324149 * 2
def baseEnd_4324149 : Nat := 2220366858658707480851107

theorem tailTrace_4324149 : CollatzResearch.WordTrace tailWord_4324149 prefixEnd_4324149 2220366858658707480851107 := by
  unfold tailWord_4324149
  simp only [CollatzResearch.WordTrace]
  refine ⟨157714670811354153698855501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105143113874236102465903667 157714670811354153698855501)
  ·
    refine ⟨59143001554257807637070813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157714670811354153698855501 59143001554257807637070813)
    ·
      refine ⟨22178625582846677863901555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59143001554257807637070813 22178625582846677863901555)
      ·
        refine ⟨33267938374270016795852333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22178625582846677863901555 33267938374270016795852333)
        ·
          refine ⟨12475476890351256298444625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33267938374270016795852333 12475476890351256298444625)
          ·
            refine ⟨9356607667763442223833469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12475476890351256298444625 9356607667763442223833469)
            ·
              refine ⟨3508727875411290833937551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9356607667763442223833469 3508727875411290833937551)
              ·
                refine ⟨5263091813116936250906327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3508727875411290833937551 5263091813116936250906327)
                ·
                  refine ⟨7894637719675404376359491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263091813116936250906327 7894637719675404376359491)
                  ·
                    refine ⟨11841956579513106564539237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7894637719675404376359491 11841956579513106564539237)
                    ·
                      refine ⟨2220366858658707480851107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11841956579513106564539237 2220366858658707480851107)
                      ·
                        rfl

theorem cell23_4324149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_4324149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324149 prefixEnd_4324149 := by exact prefixLift 4324149
  have htrace : WordTrace (prefixWord ++ tailWord_4324149) baseStart_4324149 baseEnd_4324149 := by
    simpa [prefixWord, tailWord_4324149, baseEnd_4324149] using wordTrace_append hprefix tailTrace_4324149
  have hstable : (prefixWord ++ tailWord_4324149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324149).length < 2 ^ (prefixWord ++ tailWord_4324149).sum := by decide
  have hdescent : baseEnd_4324149 < baseStart_4324149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324168 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_4324168 : Nat := 118140960795 + 4324168 * 2 ^ 59
def prefixEnd_4324168 : Nat := 4983230072969 + 3 ^ 40 * 4324168 * 2
def baseEnd_4324168 : Nat := 740125538263714302171173

theorem tailTrace_4324168 : CollatzResearch.WordTrace tailWord_4324168 prefixEnd_4324168 740125538263714302171173 := by
  unfold tailWord_4324168
  simp only [CollatzResearch.WordTrace]
  refine ⟨78857681899142659971898579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105143575865523546629198105 78857681899142659971898579)
  ·
    refine ⟨118286522848713989957847869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78857681899142659971898579 118286522848713989957847869)
    ·
      refine ⟨44357446068267746234192951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118286522848713989957847869 44357446068267746234192951)
      ·
        refine ⟨66536169102401619351289427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44357446068267746234192951 66536169102401619351289427)
        ·
          refine ⟨99804253653602429026934141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66536169102401619351289427 99804253653602429026934141)
          ·
            refine ⟨37426595120100910885100303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99804253653602429026934141 37426595120100910885100303)
            ·
              refine ⟨56139892680151366327650455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37426595120100910885100303 56139892680151366327650455)
              ·
                refine ⟨84209839020227049491475683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56139892680151366327650455 84209839020227049491475683)
                ·
                  refine ⟨126314758530340574237213525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84209839020227049491475683 126314758530340574237213525)
                  ·
                    refine ⟨740125538263714302171173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 126314758530340574237213525 740125538263714302171173)
                    ·
                      rfl

theorem cell23_4324168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_4324168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324168 prefixEnd_4324168 := by exact prefixLift 4324168
  have htrace : WordTrace (prefixWord ++ tailWord_4324168) baseStart_4324168 baseEnd_4324168 := by
    simpa [prefixWord, tailWord_4324168, baseEnd_4324168] using wordTrace_append hprefix tailTrace_4324168
  have hstable : (prefixWord ++ tailWord_4324168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324168).length < 2 ^ (prefixWord ++ tailWord_4324168).sum := by decide
  have hdescent : baseEnd_4324168 < baseStart_4324168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324192 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 3, 3, 2]
def baseStart_4324192 : Nat := 118140960795 + 4324192 * 2 ^ 59
def prefixEnd_4324192 : Nat := 4983230072969 + 3 ^ 40 * 4324192 * 2
def baseEnd_4324192 : Nat := 2220388938326850812613409

theorem tailTrace_4324192 : CollatzResearch.WordTrace tailWord_4324192 prefixEnd_4324192 2220388938326850812613409 := by
  unfold tailWord_4324192
  simp only [CollatzResearch.WordTrace]
  refine ⟨78858119575099186021335415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105144159433465581361780553 78858119575099186021335415)
  ·
    refine ⟨118287179362648779032003123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78858119575099186021335415 118287179362648779032003123)
    ·
      refine ⟨177430769043973168548004685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118287179362648779032003123 177430769043973168548004685)
      ·
        refine ⟨66536538391489938205501757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177430769043973168548004685 66536538391489938205501757)
        ·
          refine ⟨24951201896808726827063159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66536538391489938205501757 24951201896808726827063159)
          ·
            refine ⟨37426802845213090240594739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24951201896808726827063159 37426802845213090240594739)
            ·
              refine ⟨56140204267819635360892109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37426802845213090240594739 56140204267819635360892109)
              ·
                refine ⟨21052576600432363260334541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56140204267819635360892109 21052576600432363260334541)
                ·
                  refine ⟨7894716225162136222625453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21052576600432363260334541 7894716225162136222625453)
                  ·
                    refine ⟨2960518584435801083484545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7894716225162136222625453 2960518584435801083484545)
                    ·
                      refine ⟨2220388938326850812613409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960518584435801083484545 2220388938326850812613409)
                      ·
                        rfl

theorem cell23_4324192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_4324192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324192 prefixEnd_4324192 := by exact prefixLift 4324192
  have htrace : WordTrace (prefixWord ++ tailWord_4324192) baseStart_4324192 baseEnd_4324192 := by
    simpa [prefixWord, tailWord_4324192, baseEnd_4324192] using wordTrace_append hprefix tailTrace_4324192
  have hstable : (prefixWord ++ tailWord_4324192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324192).length < 2 ^ (prefixWord ++ tailWord_4324192).sum := by decide
  have hdescent : baseEnd_4324192 < baseStart_4324192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324209 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 1, 3, 2]
def baseStart_4324209 : Nat := 118140960795 + 4324209 * 2 ^ 59
def prefixEnd_4324209 : Nat := 4983230072969 + 3 ^ 40 * 4324209 * 2
def baseEnd_4324209 : Nat := 2220397667497977246100831

theorem tailTrace_4324209 : CollatzResearch.WordTrace tailWord_4324209 prefixEnd_4324209 2220397667497977246100831 := by
  unfold tailWord_4324209
  simp only [CollatzResearch.WordTrace]
  refine ⟨157716859191136783946039681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105144572794091189297359787 157716859191136783946039681)
  ·
    refine ⟨118287644393352587959529761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157716859191136783946039681 118287644393352587959529761)
    ·
      refine ⟨88715733295014440969647321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118287644393352587959529761 88715733295014440969647321)
      ·
        refine ⟨66536799971260830727235491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88715733295014440969647321 66536799971260830727235491)
        ·
          refine ⟨99805199956891246090853237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66536799971260830727235491 99805199956891246090853237)
          ·
            refine ⟨9356737495958554321017491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99805199956891246090853237 9356737495958554321017491)
            ·
              refine ⟨14035106243937831481526237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9356737495958554321017491 14035106243937831481526237)
              ·
                refine ⟨5263164841476686805572339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14035106243937831481526237 5263164841476686805572339)
                ·
                  refine ⟨7894747262215030208358509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263164841476686805572339 7894747262215030208358509)
                  ·
                    refine ⟨2960530223330636328134441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7894747262215030208358509 2960530223330636328134441)
                    ·
                      refine ⟨2220397667497977246100831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960530223330636328134441 2220397667497977246100831)
                      ·
                        rfl

theorem cell23_4324209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_4324209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324209 prefixEnd_4324209 := by exact prefixLift 4324209
  have htrace : WordTrace (prefixWord ++ tailWord_4324209) baseStart_4324209 baseEnd_4324209 := by
    simpa [prefixWord, tailWord_4324209, baseEnd_4324209] using wordTrace_append hprefix tailTrace_4324209
  have hstable : (prefixWord ++ tailWord_4324209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324209).length < 2 ^ (prefixWord ++ tailWord_4324209).sum := by decide
  have hdescent : baseEnd_4324209 < baseStart_4324209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324235 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4]
def baseStart_4324235 : Nat := 118140960795 + 4324235 * 2 ^ 59
def prefixEnd_4324235 : Nat := 4983230072969 + 3 ^ 40 * 4324235 * 2
def baseEnd_4324235 : Nat := 2220411017994994144375711

theorem tailTrace_4324235 : CollatzResearch.WordTrace tailWord_4324235 prefixEnd_4324235 2220411017994994144375711 := by
  unfold tailWord_4324235
  simp only [CollatzResearch.WordTrace]
  refine ⟨157717807489042590386486159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105145204992695060257657439 157717807489042590386486159)
  ·
    refine ⟨236576711233563885579729239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157717807489042590386486159 236576711233563885579729239)
    ·
      refine ⟨354865066850345828369593859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236576711233563885579729239 354865066850345828369593859)
      ·
        refine ⟨532297600275518742554390789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354865066850345828369593859 532297600275518742554390789)
        ·
          refine ⟨99805800051659764228948273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 532297600275518742554390789 99805800051659764228948273)
          ·
            refine ⟨74854350038744823171711205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99805800051659764228948273 74854350038744823171711205)
            ·
              refine ⟨14035190632264654344695851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74854350038744823171711205 14035190632264654344695851)
              ·
                refine ⟨21052785948396981517043777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14035190632264654344695851 21052785948396981517043777)
                ·
                  refine ⟨15789589461297736137782833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21052785948396981517043777 15789589461297736137782833)
                  ·
                    refine ⟨11842192095973302103337125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15789589461297736137782833 11842192095973302103337125)
                    ·
                      refine ⟨2220411017994994144375711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11842192095973302103337125 2220411017994994144375711)
                      ·
                        rfl

theorem cell23_4324235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_4324235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324235 prefixEnd_4324235 := by exact prefixLift 4324235
  have htrace : WordTrace (prefixWord ++ tailWord_4324235) baseStart_4324235 baseEnd_4324235 := by
    simpa [prefixWord, tailWord_4324235, baseEnd_4324235] using wordTrace_append hprefix tailTrace_4324235
  have hstable : (prefixWord ++ tailWord_4324235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324235).length < 2 ^ (prefixWord ++ tailWord_4324235).sum := by decide
  have hdescent : baseEnd_4324235 < baseStart_4324235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324245 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 7]
def baseStart_4324245 : Nat := 118140960795 + 4324245 * 2 ^ 59
def prefixEnd_4324245 : Nat := 4983230072969 + 3 ^ 40 * 4324245 * 2
def baseEnd_4324245 : Nat := 246712905866837678361185

theorem tailTrace_4324245 : CollatzResearch.WordTrace tailWord_4324245 prefixEnd_4324245 246712905866837678361185 := by
  unfold tailWord_4324245
  simp only [CollatzResearch.WordTrace]
  refine ⟨157718172219006362094350189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105145448146004241396233459 157718172219006362094350189)
  ·
    refine ⟨59144314582127385785381321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157718172219006362094350189 59144314582127385785381321)
    ·
      refine ⟨44358235936595539339035991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59144314582127385785381321 44358235936595539339035991)
      ·
        refine ⟨66537353904893309008553987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44358235936595539339035991 66537353904893309008553987)
        ·
          refine ⟨99806030857339963512830981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66537353904893309008553987 99806030857339963512830981)
          ·
            refine ⟨18713630785751243158655809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99806030857339963512830981 18713630785751243158655809)
            ·
              refine ⟨14035223089313432368991857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18713630785751243158655809 14035223089313432368991857)
              ·
                refine ⟨10526417316985074276743893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14035223089313432368991857 10526417316985074276743893)
                ·
                  refine ⟨246712905866837678361185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10526417316985074276743893 246712905866837678361185)
                  ·
                    rfl

theorem cell23_4324245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_4324245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324245 prefixEnd_4324245 := by exact prefixLift 4324245
  have htrace : WordTrace (prefixWord ++ tailWord_4324245) baseStart_4324245 baseEnd_4324245 := by
    simpa [prefixWord, tailWord_4324245, baseEnd_4324245] using wordTrace_append hprefix tailTrace_4324245
  have hstable : (prefixWord ++ tailWord_4324245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324245).length < 2 ^ (prefixWord ++ tailWord_4324245).sum := by decide
  have hdescent : baseEnd_4324245 < baseStart_4324245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324282 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2]
def baseStart_4324282 : Nat := 118140960795 + 4324282 * 2 ^ 59
def prefixEnd_4324282 : Nat := 4983230072969 + 3 ^ 40 * 4324282 * 2
def baseEnd_4324282 : Nat := 2220435151585755460487995

theorem tailTrace_4324282 : CollatzResearch.WordTrace tailWord_4324282 prefixEnd_4324282 2220435151585755460487995 := by
  unfold tailWord_4324282
  simp only [CollatzResearch.WordTrace]
  refine ⟨39429880429968079353361775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105146347813248211608964733 39429880429968079353361775)
  ·
    refine ⟨59144820644952119030042663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39429880429968079353361775 59144820644952119030042663)
    ·
      refine ⟨88717230967428178545063995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59144820644952119030042663 88717230967428178545063995)
      ·
        refine ⟨133075846451142267817595993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88717230967428178545063995 133075846451142267817595993)
        ·
          refine ⟨99806884838356700863196995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133075846451142267817595993 99806884838356700863196995)
          ·
            refine ⟨149710327257535051294795493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99806884838356700863196995 149710327257535051294795493)
            ·
              refine ⟨28070686360787822117774155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149710327257535051294795493 28070686360787822117774155)
              ·
                refine ⟨42106029541181733176661233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28070686360787822117774155 42106029541181733176661233)
                ·
                  refine ⟨31579522155886299882495925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42106029541181733176661233 31579522155886299882495925)
                  ·
                    refine ⟨2960580202114340613983993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31579522155886299882495925 2960580202114340613983993)
                    ·
                      refine ⟨2220435151585755460487995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960580202114340613983993 2220435151585755460487995)
                      ·
                        rfl

theorem cell23_4324282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_4324282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324282 prefixEnd_4324282 := by exact prefixLift 4324282
  have htrace : WordTrace (prefixWord ++ tailWord_4324282) baseStart_4324282 baseEnd_4324282 := by
    simpa [prefixWord, tailWord_4324282, baseEnd_4324282] using wordTrace_append hprefix tailTrace_4324282
  have hstable : (prefixWord ++ tailWord_4324282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324282).length < 2 ^ (prefixWord ++ tailWord_4324282).sum := by decide
  have hdescent : baseEnd_4324282 < baseStart_4324282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324294 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4324294 : Nat := 118140960795 + 4324294 * 2 ^ 59
def prefixEnd_4324294 : Nat := 4983230072969 + 3 ^ 40 * 4324294 * 2
def baseEnd_4324294 : Nat := 2220441313353609413537941

theorem tailTrace_4324294 : CollatzResearch.WordTrace tailWord_4324294 prefixEnd_4324294 2220441313353609413537941 := by
  unfold tailWord_4324294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928748731119651358215123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105146639597219228975255957 4928748731119651358215123)
  ·
    refine ⟨7393123096679477037322685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4928748731119651358215123 7393123096679477037322685)
    ·
      refine ⟨2772421161254803888996007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7393123096679477037322685 2772421161254803888996007)
      ·
        refine ⟨4158631741882205833494011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772421161254803888996007 4158631741882205833494011)
        ·
          refine ⟨6237947612823308750241017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158631741882205833494011 6237947612823308750241017)
          ·
            refine ⟨4678460709617481562680763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6237947612823308750241017 4678460709617481562680763)
            ·
              refine ⟨7017691064426222344021145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678460709617481562680763 7017691064426222344021145)
              ·
                refine ⟨5263268298319666758015859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7017691064426222344021145 5263268298319666758015859)
                ·
                  refine ⟨7894902447479500137023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263268298319666758015859 7894902447479500137023789)
                  ·
                    refine ⟨2960588417804812551383921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7894902447479500137023789 2960588417804812551383921)
                    ·
                      refine ⟨2220441313353609413537941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960588417804812551383921 2220441313353609413537941)
                      ·
                        rfl

theorem cell23_4324294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4324294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324294 prefixEnd_4324294 := by exact prefixLift 4324294
  have htrace : WordTrace (prefixWord ++ tailWord_4324294) baseStart_4324294 baseEnd_4324294 := by
    simpa [prefixWord, tailWord_4324294, baseEnd_4324294] using wordTrace_append hprefix tailTrace_4324294
  have hstable : (prefixWord ++ tailWord_4324294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324294).length < 2 ^ (prefixWord ++ tailWord_4324294).sum := by decide
  have hdescent : baseEnd_4324294 < baseStart_4324294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324295 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_4324295 : Nat := 118140960795 + 4324295 * 2 ^ 59
def prefixEnd_4324295 : Nat := 4983230072969 + 3 ^ 40 * 4324295 * 2
def baseEnd_4324295 : Nat := 2220441826834263909625435

theorem tailTrace_4324295 : CollatzResearch.WordTrace tailWord_4324295 prefixEnd_4324295 2220441826834263909625435 := by
  unfold tailWord_4324295
  simp only [CollatzResearch.WordTrace]
  refine ⟨157719995868825220633670339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105146663912550147089113559 157719995868825220633670339)
  ·
    refine ⟨236579993803237830950505509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157719995868825220633670339 236579993803237830950505509)
    ·
      refine ⟨44358748838107093303219783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236579993803237830950505509 44358748838107093303219783)
      ·
        refine ⟨66538123257160639954829675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44358748838107093303219783 66538123257160639954829675)
        ·
          refine ⟨99807184885740959932244513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66538123257160639954829675 99807184885740959932244513)
          ·
            refine ⟨74855388664305719949183385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99807184885740959932244513 74855388664305719949183385)
            ·
              refine ⟨56141541498229289961887539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74855388664305719949183385 56141541498229289961887539)
              ·
                refine ⟨84212312247343934942831309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56141541498229289961887539 84212312247343934942831309)
                ·
                  refine ⟨31579617092753975603561741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84212312247343934942831309 31579617092753975603561741)
                  ·
                    refine ⟨11842356409782740851335653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31579617092753975603561741 11842356409782740851335653)
                    ·
                      refine ⟨2220441826834263909625435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11842356409782740851335653 2220441826834263909625435)
                      ·
                        rfl

theorem cell23_4324295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_4324295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324295 prefixEnd_4324295 := by exact prefixLift 4324295
  have htrace : WordTrace (prefixWord ++ tailWord_4324295) baseStart_4324295 baseEnd_4324295 := by
    simpa [prefixWord, tailWord_4324295, baseEnd_4324295] using wordTrace_append hprefix tailTrace_4324295
  have hstable : (prefixWord ++ tailWord_4324295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324295).length < 2 ^ (prefixWord ++ tailWord_4324295).sum := by decide
  have hdescent : baseEnd_4324295 < baseStart_4324295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324309 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_4324309 : Nat := 118140960795 + 4324309 * 2 ^ 59
def prefixEnd_4324309 : Nat := 4983230072969 + 3 ^ 40 * 4324309 * 2
def baseEnd_4324309 : Nat := 740149671854475618283457

theorem tailTrace_4324309 : CollatzResearch.WordTrace tailWord_4324309 prefixEnd_4324309 740149671854475618283457 := by
  unfold tailWord_4324309
  simp only [CollatzResearch.WordTrace]
  refine ⟨157720506490774501024679981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105147004327183000683119987 157720506490774501024679981)
  ·
    refine ⟨59145189934040437884254993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157720506490774501024679981 59145189934040437884254993)
    ·
      refine ⟨44358892450530328413191245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59145189934040437884254993 44358892450530328413191245)
      ·
        refine ⟨16634584668948873154946717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44358892450530328413191245 16634584668948873154946717)
        ·
          refine ⟨6237969250855827433105019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16634584668948873154946717 6237969250855827433105019)
          ·
            refine ⟨9356953876283741149657529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6237969250855827433105019 9356953876283741149657529)
            ·
              refine ⟨7017715407212805862243147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9356953876283741149657529 7017715407212805862243147)
              ·
                refine ⟨10526573110819208793364721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7017715407212805862243147 10526573110819208793364721)
                ·
                  refine ⟨7894929833114406595023541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10526573110819208793364721 7894929833114406595023541)
                  ·
                    refine ⟨740149671854475618283457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7894929833114406595023541 740149671854475618283457)
                    ·
                      rfl

theorem cell23_4324309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_4324309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324309 prefixEnd_4324309 := by exact prefixLift 4324309
  have htrace : WordTrace (prefixWord ++ tailWord_4324309) baseStart_4324309 baseEnd_4324309 := by
    simpa [prefixWord, tailWord_4324309, baseEnd_4324309] using wordTrace_append hprefix tailTrace_4324309
  have hstable : (prefixWord ++ tailWord_4324309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324309).length < 2 ^ (prefixWord ++ tailWord_4324309).sum := by decide
  have hdescent : baseEnd_4324309 < baseStart_4324309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324312 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_4324312 : Nat := 118140960795 + 4324312 * 2 ^ 59
def prefixEnd_4324312 : Nat := 4983230072969 + 3 ^ 40 * 4324312 * 2
def baseEnd_4324312 : Nat := 2220450556005390343112857

theorem tailTrace_4324312 : CollatzResearch.WordTrace tailWord_4324312 prefixEnd_4324312 2220450556005390343112857 := by
  unfold tailWord_4324312
  simp only [CollatzResearch.WordTrace]
  refine ⟨78860307954881816268519595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105147077273175755024692793 78860307954881816268519595)
  ·
    refine ⟨118290461932322724402779393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78860307954881816268519595 118290461932322724402779393)
    ·
      refine ⟨88717846449242043302084545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118290461932322724402779393 88717846449242043302084545)
      ·
        refine ⟨66538384836931532476563409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88717846449242043302084545 66538384836931532476563409)
        ·
          refine ⟨49903788627698649357422557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66538384836931532476563409 49903788627698649357422557)
          ·
            refine ⟨18713920735386993509033459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49903788627698649357422557 18713920735386993509033459)
            ·
              refine ⟨28070881103080490263550189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18713920735386993509033459 28070881103080490263550189)
              ·
                refine ⟨10526580413655183848831321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28070881103080490263550189 10526580413655183848831321)
                ·
                  refine ⟨7894935310241387886623491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10526580413655183848831321 7894935310241387886623491)
                  ·
                    refine ⟨11842402965362081829935237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7894935310241387886623491 11842402965362081829935237)
                    ·
                      refine ⟨2220450556005390343112857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11842402965362081829935237 2220450556005390343112857)
                      ·
                        rfl

theorem cell23_4324312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_4324312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324312 prefixEnd_4324312 := by exact prefixLift 4324312
  have htrace : WordTrace (prefixWord ++ tailWord_4324312) baseStart_4324312 baseEnd_4324312 := by
    simpa [prefixWord, tailWord_4324312, baseEnd_4324312] using wordTrace_append hprefix tailTrace_4324312
  have hstable : (prefixWord ++ tailWord_4324312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324312).length < 2 ^ (prefixWord ++ tailWord_4324312).sum := by decide
  have hdescent : baseEnd_4324312 < baseStart_4324312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 3]
def baseStart_4324315 : Nat := 118140960795 + 4324315 * 2 ^ 59
def prefixEnd_4324315 : Nat := 4983230072969 + 3 ^ 40 * 4324315 * 2
def baseEnd_4324315 : Nat := 2220452096447353831375343

theorem tailTrace_4324315 : CollatzResearch.WordTrace tailWord_4324315 prefixEnd_4324315 2220452096447353831375343 := by
  unfold tailWord_4324315
  simp only [CollatzResearch.WordTrace]
  refine ⟨157720725328752764049398399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105147150219168509366265599 157720725328752764049398399)
  ·
    refine ⟨236581087993129146074097599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157720725328752764049398399 236581087993129146074097599)
    ·
      refine ⟨354871631989693719111146399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236581087993129146074097599 354871631989693719111146399)
      ·
        refine ⟨532307447984540578666719599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354871631989693719111146399 532307447984540578666719599)
        ·
          refine ⟨798461171976810868000079399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532307447984540578666719599 798461171976810868000079399)
          ·
            refine ⟨1197691757965216302000119099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798461171976810868000079399 1197691757965216302000119099)
            ·
              refine ⟨1796537636947824453000178649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197691757965216302000119099 1796537636947824453000178649)
              ·
                refine ⟨1347403227710868339750133987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1796537636947824453000178649 1347403227710868339750133987)
                ·
                  refine ⟨2021104841566302509625200981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347403227710868339750133987 2021104841566302509625200981)
                  ·
                    refine ⟨5921205590526276883667581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 2021104841566302509625200981 5921205590526276883667581)
                    ·
                      refine ⟨2220452096447353831375343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921205590526276883667581 2220452096447353831375343)
                      ·
                        rfl

theorem cell23_4324315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 3].length) (baseStart_4324315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324315 prefixEnd_4324315 := by exact prefixLift 4324315
  have htrace : WordTrace (prefixWord ++ tailWord_4324315) baseStart_4324315 baseEnd_4324315 := by
    simpa [prefixWord, tailWord_4324315, baseEnd_4324315] using wordTrace_append hprefix tailTrace_4324315
  have hstable : (prefixWord ++ tailWord_4324315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324315).length < 2 ^ (prefixWord ++ tailWord_4324315).sum := by decide
  have hdescent : baseEnd_4324315 < baseStart_4324315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324340 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4324340 : Nat := 118140960795 + 4324340 * 2 ^ 59
def prefixEnd_4324340 : Nat := 4983230072969 + 3 ^ 40 * 4324340 * 2
def baseEnd_4324340 : Nat := 2220464933463716233562729

theorem tailTrace_4324340 : CollatzResearch.WordTrace tailWord_4324340 prefixEnd_4324340 2220464933463716233562729 := by
  unfold tailWord_4324340
  simp only [CollatzResearch.WordTrace]
  refine ⟨78860818576831096659529237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105147758102441462212705649 78860818576831096659529237)
  ·
    refine ⟨3696600870788957655915433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78860818576831096659529237 3696600870788957655915433)
    ·
      refine ⟨2772450653091718241936575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3696600870788957655915433 2772450653091718241936575)
      ·
        refine ⟨4158675979637577362904863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772450653091718241936575 4158675979637577362904863)
        ·
          refine ⟨6238013969456366044357295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4158675979637577362904863 6238013969456366044357295)
          ·
            refine ⟨9357020954184549066535943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238013969456366044357295 9357020954184549066535943)
            ·
              refine ⟨14035531431276823599803915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9357020954184549066535943 14035531431276823599803915)
              ·
                refine ⟨21053297146915235399705873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14035531431276823599803915 21053297146915235399705873)
                ·
                  refine ⟨15789972860186426549779405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21053297146915235399705873 15789972860186426549779405)
                  ·
                    refine ⟨5921239822569909956167277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15789972860186426549779405 5921239822569909956167277)
                    ·
                      refine ⟨2220464933463716233562729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921239822569909956167277 2220464933463716233562729)
                      ·
                        rfl

theorem cell23_4324340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4324340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324340 prefixEnd_4324340 := by exact prefixLift 4324340
  have htrace : WordTrace (prefixWord ++ tailWord_4324340) baseStart_4324340 baseEnd_4324340 := by
    simpa [prefixWord, tailWord_4324340, baseEnd_4324340] using wordTrace_append hprefix tailTrace_4324340
  have hstable : (prefixWord ++ tailWord_4324340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324340).length < 2 ^ (prefixWord ++ tailWord_4324340).sum := by decide
  have hdescent : baseEnd_4324340 < baseStart_4324340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324366 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4324366 : Nat := 118140960795 + 4324366 * 2 ^ 59
def prefixEnd_4324366 : Nat := 4983230072969 + 3 ^ 40 * 4324366 * 2
def baseEnd_4324366 : Nat := 2220478283960733131837609

theorem tailTrace_4324366 : CollatzResearch.WordTrace tailWord_4324366 prefixEnd_4324366 2220478283960733131837609 := by
  unfold tailWord_4324366
  simp only [CollatzResearch.WordTrace]
  refine ⟨19715323181445999969938119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105148390301045333173003301 19715323181445999969938119)
  ·
    refine ⟨29572984772168999954907179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19715323181445999969938119 29572984772168999954907179)
    ·
      refine ⟨44359477158253499932360769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29572984772168999954907179 44359477158253499932360769)
      ·
        refine ⟨33269607868690124949270577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44359477158253499932360769 33269607868690124949270577)
        ·
          refine ⟨24952205901517593711952933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33269607868690124949270577 24952205901517593711952933)
          ·
            refine ⟨4678538606534548820991175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24952205901517593711952933 4678538606534548820991175)
            ·
              refine ⟨7017807909801823231486763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678538606534548820991175 7017807909801823231486763)
              ·
                refine ⟨10526711864702734847230145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7017807909801823231486763 10526711864702734847230145)
                ·
                  refine ⟨7895033898527051135422609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10526711864702734847230145 7895033898527051135422609)
                  ·
                    refine ⟨5921275423895288351566957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7895033898527051135422609 5921275423895288351566957)
                    ·
                      refine ⟨2220478283960733131837609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921275423895288351566957 2220478283960733131837609)
                      ·
                        rfl

theorem cell23_4324366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4324366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324366 prefixEnd_4324366 := by exact prefixLift 4324366
  have htrace : WordTrace (prefixWord ++ tailWord_4324366) baseStart_4324366 baseEnd_4324366 := by
    simpa [prefixWord, tailWord_4324366, baseEnd_4324366] using wordTrace_append hprefix tailTrace_4324366
  have hstable : (prefixWord ++ tailWord_4324366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324366).length < 2 ^ (prefixWord ++ tailWord_4324366).sum := by decide
  have hdescent : baseEnd_4324366 < baseStart_4324366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324389 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 4, 3, 2]
def baseStart_4324389 : Nat := 118140960795 + 4324389 * 2 ^ 59
def prefixEnd_4324389 : Nat := 4983230072969 + 3 ^ 40 * 4324389 * 2
def baseEnd_4324389 : Nat := 2220490094015786541850003

theorem tailTrace_4324389 : CollatzResearch.WordTrace tailWord_4324389 prefixEnd_4324389 2220490094015786541850003 := by
  unfold tailWord_4324389
  simp only [CollatzResearch.WordTrace]
  refine ⟨157723424330484674687592221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105148949553656449791728147 157723424330484674687592221)
  ·
    refine ⟨59146284123931753007847083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157723424330484674687592221 59146284123931753007847083)
    ·
      refine ⟨88719426185897629511770625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59146284123931753007847083 88719426185897629511770625)
      ·
        refine ⟨66539569639423222133827969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88719426185897629511770625 66539569639423222133827969)
        ·
          refine ⟨49904677229567416600370977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66539569639423222133827969 49904677229567416600370977)
          ·
            refine ⟨37428507922175562450278233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49904677229567416600370977 37428507922175562450278233)
            ·
              refine ⟨28071380941631671837708675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37428507922175562450278233 28071380941631671837708675)
              ·
                refine ⟨42107071412447507756563013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28071380941631671837708675 42107071412447507756563013)
                ·
                  refine ⟨7895075889833907704355565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42107071412447507756563013 7895075889833907704355565)
                  ·
                    refine ⟨2960653458687715389133337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7895075889833907704355565 2960653458687715389133337)
                    ·
                      refine ⟨2220490094015786541850003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960653458687715389133337 2220490094015786541850003)
                      ·
                        rfl

theorem cell23_4324389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_4324389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324389 prefixEnd_4324389 := by exact prefixLift 4324389
  have htrace : WordTrace (prefixWord ++ tailWord_4324389) baseStart_4324389 baseEnd_4324389 := by
    simpa [prefixWord, tailWord_4324389, baseEnd_4324389] using wordTrace_append hprefix tailTrace_4324389
  have hstable : (prefixWord ++ tailWord_4324389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324389).length < 2 ^ (prefixWord ++ tailWord_4324389).sum := by decide
  have hdescent : baseEnd_4324389 < baseStart_4324389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324396 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 1, 1, 3]
def baseStart_4324396 : Nat := 118140960795 + 4324396 * 2 ^ 59
def prefixEnd_4324396 : Nat := 4983230072969 + 3 ^ 40 * 4324396 * 2
def baseEnd_4324396 : Nat := 2220493688380368014462471

theorem tailTrace_4324396 : CollatzResearch.WordTrace tailWord_4324396 prefixEnd_4324396 2220493688380368014462471 := by
  unfold tailWord_4324396
  simp only [CollatzResearch.WordTrace]
  refine ⟨78861839820729657441548521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105149119760972876588731361 78861839820729657441548521)
  ·
    refine ⟨59146379865547243081161391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78861839820729657441548521 59146379865547243081161391)
    ·
      refine ⟨88719569798320864621742087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59146379865547243081161391 88719569798320864621742087)
      ·
        refine ⟨133079354697481296932613131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88719569798320864621742087 133079354697481296932613131)
        ·
          refine ⟨199619032046221945398919697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133079354697481296932613131 199619032046221945398919697)
          ·
            refine ⟨149714274034666459049189773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199619032046221945398919697 149714274034666459049189773)
            ·
              refine ⟨56142852762999922143446165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149714274034666459049189773 56142852762999922143446165)
              ·
                refine ⟨2631696223265621350474039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56142852762999922143446165 2631696223265621350474039)
                ·
                  refine ⟨3947544334898432025711059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631696223265621350474039 3947544334898432025711059)
                  ·
                    refine ⟨5921316502347648038566589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947544334898432025711059 5921316502347648038566589)
                    ·
                      refine ⟨2220493688380368014462471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921316502347648038566589 2220493688380368014462471)
                      ·
                        rfl

theorem cell23_4324396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_4324396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324396 prefixEnd_4324396 := by exact prefixLift 4324396
  have htrace : WordTrace (prefixWord ++ tailWord_4324396) baseStart_4324396 baseEnd_4324396 := by
    simpa [prefixWord, tailWord_4324396, baseEnd_4324396] using wordTrace_append hprefix tailTrace_4324396
  have hstable : (prefixWord ++ tailWord_4324396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324396).length < 2 ^ (prefixWord ++ tailWord_4324396).sum := by decide
  have hdescent : baseEnd_4324396 < baseStart_4324396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324406 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_4324406 : Nat := 118140960795 + 4324406 * 2 ^ 59
def prefixEnd_4324406 : Nat := 4983230072969 + 3 ^ 40 * 4324406 * 2
def baseEnd_4324406 : Nat := 2220498823186912975337425

theorem tailTrace_4324406 : CollatzResearch.WordTrace tailWord_4324406 prefixEnd_4324406 2220498823186912975337425 := by
  unfold tailWord_4324406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9857752773213942911935067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105149362914282057727307381 9857752773213942911935067)
  ·
    refine ⟨14786629159820914367902601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9857752773213942911935067 14786629159820914367902601)
    ·
      refine ⟨11089971869865685775926951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14786629159820914367902601 11089971869865685775926951)
      ·
        refine ⟨16634957804798528663890427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11089971869865685775926951 16634957804798528663890427)
        ·
          refine ⟨24952436707197792995835641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16634957804798528663890427 24952436707197792995835641)
          ·
            refine ⟨18714327530398344746876731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24952436707197792995835641 18714327530398344746876731)
            ·
              refine ⟨28071491295597517120315097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18714327530398344746876731 28071491295597517120315097)
              ·
                refine ⟨21053618471698137840236323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28071491295597517120315097 21053618471698137840236323)
                ·
                  refine ⟨31580427707547206760354485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21053618471698137840236323 31580427707547206760354485)
                  ·
                    refine ⟨2960665097582550633783233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31580427707547206760354485 2960665097582550633783233)
                    ·
                      refine ⟨2220498823186912975337425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960665097582550633783233 2220498823186912975337425)
                      ·
                        rfl

theorem cell23_4324406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_4324406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324406 prefixEnd_4324406 := by exact prefixLift 4324406
  have htrace : WordTrace (prefixWord ++ tailWord_4324406) baseStart_4324406 baseEnd_4324406 := by
    simpa [prefixWord, tailWord_4324406, baseEnd_4324406] using wordTrace_append hprefix tailTrace_4324406
  have hstable : (prefixWord ++ tailWord_4324406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324406).length < 2 ^ (prefixWord ++ tailWord_4324406).sum := by decide
  have hdescent : baseEnd_4324406 < baseStart_4324406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324419 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 4]
def baseStart_4324419 : Nat := 118140960795 + 4324419 * 2 ^ 59
def prefixEnd_4324419 : Nat := 4983230072969 + 3 ^ 40 * 4324419 * 2
def baseEnd_4324419 : Nat := 2220505498435421424474865

theorem tailTrace_4324419 : CollatzResearch.WordTrace tailWord_4324419 prefixEnd_4324419 2220505498435421424474865 := by
  unfold tailWord_4324419
  simp only [CollatzResearch.WordTrace]
  refine ⟨157724518520375989811184311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105149679013583993207456207 157724518520375989811184311)
  ·
    refine ⟨236586777780563984716776467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157724518520375989811184311 236586777780563984716776467)
    ·
      refine ⟨354880166670845977075164701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236586777780563984716776467 354880166670845977075164701)
      ·
        refine ⟨133080062501567241403186763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354880166670845977075164701 133080062501567241403186763)
        ·
          refine ⟨199620093752350862104780145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133080062501567241403186763 199620093752350862104780145)
          ·
            refine ⟨149715070314263146578585109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199620093752350862104780145 149715070314263146578585109)
            ·
              refine ⟨7017893920981084995871177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149715070314263146578585109 7017893920981084995871177)
              ·
                refine ⟨5263420440735813746903383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7017893920981084995871177 5263420440735813746903383)
                ·
                  refine ⟨7895130661103720620355075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263420440735813746903383 7895130661103720620355075)
                  ·
                    refine ⟨11842695991655580930532613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7895130661103720620355075 11842695991655580930532613)
                    ·
                      refine ⟨2220505498435421424474865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11842695991655580930532613 2220505498435421424474865)
                      ·
                        rfl

theorem cell23_4324419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_4324419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324419 prefixEnd_4324419 := by exact prefixLift 4324419
  have htrace : WordTrace (prefixWord ++ tailWord_4324419) baseStart_4324419 baseEnd_4324419 := by
    simpa [prefixWord, tailWord_4324419, baseEnd_4324419] using wordTrace_append hprefix tailTrace_4324419
  have hstable : (prefixWord ++ tailWord_4324419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324419).length < 2 ^ (prefixWord ++ tailWord_4324419).sum := by decide
  have hdescent : baseEnd_4324419 < baseStart_4324419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324432 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_4324432 : Nat := 118140960795 + 4324432 * 2 ^ 59
def prefixEnd_4324432 : Nat := 4983230072969 + 3 ^ 40 * 4324432 * 2
def baseEnd_4324432 : Nat := 2220512173683929873612305

theorem tailTrace_4324432 : CollatzResearch.WordTrace tailWord_4324432 prefixEnd_4324432 2220512173683929873612305 := by
  unfold tailWord_4324432
  simp only [CollatzResearch.WordTrace]
  refine ⟨78862496334664446515703775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105149995112885928687605033 78862496334664446515703775)
  ·
    refine ⟨118293744501996669773555663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78862496334664446515703775 118293744501996669773555663)
    ·
      refine ⟨177440616752995004660333495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118293744501996669773555663 177440616752995004660333495)
      ·
        refine ⟨266160925129492506990500243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177440616752995004660333495 266160925129492506990500243)
        ·
          refine ⟨399241387694238760485750365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266160925129492506990500243 399241387694238760485750365)
          ·
            refine ⟨149715520385339535182156387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 399241387694238760485750365 149715520385339535182156387)
            ·
              refine ⟨224573280578009302773234581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149715520385339535182156387 224573280578009302773234581)
              ·
                refine ⟨10526872527094186067495371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 224573280578009302773234581 10526872527094186067495371)
                ·
                  refine ⟨15790308790641279101243057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10526872527094186067495371 15790308790641279101243057)
                  ·
                    refine ⟨11842731592980959325932293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15790308790641279101243057 11842731592980959325932293)
                    ·
                      refine ⟨2220512173683929873612305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11842731592980959325932293 2220512173683929873612305)
                      ·
                        rfl

theorem cell23_4324432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_4324432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324432 prefixEnd_4324432 := by exact prefixLift 4324432
  have htrace : WordTrace (prefixWord ++ tailWord_4324432) baseStart_4324432 baseEnd_4324432 := by
    simpa [prefixWord, tailWord_4324432, baseEnd_4324432] using wordTrace_append hprefix tailTrace_4324432
  have hstable : (prefixWord ++ tailWord_4324432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324432).length < 2 ^ (prefixWord ++ tailWord_4324432).sum := by decide
  have hdescent : baseEnd_4324432 < baseStart_4324432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324436 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_4324436 : Nat := 118140960795 + 4324436 * 2 ^ 59
def prefixEnd_4324436 : Nat := 4983230072969 + 3 ^ 40 * 4324436 * 2
def baseEnd_4324436 : Nat := 2220514227606547857962287

theorem tailTrace_4324436 : CollatzResearch.WordTrace tailWord_4324436 prefixEnd_4324436 2220514227606547857962287 := by
  unfold tailWord_4324436
  simp only [CollatzResearch.WordTrace]
  refine ⟨78862569280657200857276581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105150092374209601143035441 78862569280657200857276581)
  ·
    refine ⟨14786731740123225160739359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78862569280657200857276581 14786731740123225160739359)
    ·
      refine ⟨22180097610184837741109039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14786731740123225160739359 22180097610184837741109039)
      ·
        refine ⟨33270146415277256611663559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22180097610184837741109039 33270146415277256611663559)
        ·
          refine ⟨49905219622915884917495339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33270146415277256611663559 49905219622915884917495339)
          ·
            refine ⟨74857829434373827376243009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49905219622915884917495339 74857829434373827376243009)
            ·
              refine ⟨56143372075780370532182257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74857829434373827376243009 56143372075780370532182257)
              ·
                refine ⟨42107529056835277899136693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56143372075780370532182257 42107529056835277899136693)
                ·
                  refine ⟨3947580849078307303044065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42107529056835277899136693 3947580849078307303044065)
                  ·
                    refine ⟨2960685636808730477283049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3947580849078307303044065 2960685636808730477283049)
                    ·
                      refine ⟨2220514227606547857962287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960685636808730477283049 2220514227606547857962287)
                      ·
                        rfl

theorem cell23_4324436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_4324436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324436 prefixEnd_4324436 := by exact prefixLift 4324436
  have htrace : WordTrace (prefixWord ++ tailWord_4324436) baseStart_4324436 baseEnd_4324436 := by
    simpa [prefixWord, tailWord_4324436, baseEnd_4324436] using wordTrace_append hprefix tailTrace_4324436
  have hstable : (prefixWord ++ tailWord_4324436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324436).length < 2 ^ (prefixWord ++ tailWord_4324436).sum := by decide
  have hdescent : baseEnd_4324436 < baseStart_4324436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324473 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 3]
def baseStart_4324473 : Nat := 118140960795 + 4324473 * 2 ^ 59
def prefixEnd_4324473 : Nat := 4983230072969 + 3 ^ 40 * 4324473 * 2
def baseEnd_4324473 : Nat := 2220533226390764213199617

theorem tailTrace_4324473 : CollatzResearch.WordTrace tailWord_4324473 prefixEnd_4324473 2220533226390764213199617 := by
  unfold tailWord_4324473
  simp only [CollatzResearch.WordTrace]
  refine ⟨157726488062180357033650073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105150992041453571355766715 157726488062180357033650073)
  ·
    refine ⟨118294866046635267775237555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157726488062180357033650073 118294866046635267775237555)
    ·
      refine ⟨177442299069952901662856333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118294866046635267775237555 177442299069952901662856333)
      ·
        refine ⟨66540862151232338123571125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177442299069952901662856333 66540862151232338123571125)
        ·
          refine ⟨6238205826678031699084793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66540862151232338123571125 6238205826678031699084793)
          ·
            refine ⟨4678654370008523774313595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6238205826678031699084793 4678654370008523774313595)
            ·
              refine ⟨7017981555012785661470393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678654370008523774313595 7017981555012785661470393)
              ·
                refine ⟨5263486166259589246102795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7017981555012785661470393 5263486166259589246102795)
                ·
                  refine ⟨7895229249389383869154193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5263486166259589246102795 7895229249389383869154193)
                  ·
                    refine ⟨5921421937042037901865645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7895229249389383869154193 5921421937042037901865645)
                    ·
                      refine ⟨2220533226390764213199617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921421937042037901865645 2220533226390764213199617)
                      ·
                        rfl

theorem cell23_4324473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_4324473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324473 prefixEnd_4324473 := by exact prefixLift 4324473
  have htrace : WordTrace (prefixWord ++ tailWord_4324473) baseStart_4324473 baseEnd_4324473 := by
    simpa [prefixWord, tailWord_4324473, baseEnd_4324473] using wordTrace_append hprefix tailTrace_4324473
  have hstable : (prefixWord ++ tailWord_4324473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324473).length < 2 ^ (prefixWord ++ tailWord_4324473).sum := by decide
  have hdescent : baseEnd_4324473 < baseStart_4324473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324492 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_4324492 : Nat := 118140960795 + 4324492 * 2 ^ 59
def prefixEnd_4324492 : Nat := 4983230072969 + 3 ^ 40 * 4324492 * 2
def baseEnd_4324492 : Nat := 2220542982523199638862029

theorem tailTrace_4324492 : CollatzResearch.WordTrace tailWord_4324492 prefixEnd_4324492 2220542982523199638862029 := by
  unfold tailWord_4324492
  simp only [CollatzResearch.WordTrace]
  refine ⟨78863590524555761639295865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105151454032741015519061153 78863590524555761639295865)
  ·
    refine ⟨59147692893416821229471899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78863590524555761639295865 59147692893416821229471899)
    ·
      refine ⟨88721539340125231844207849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59147692893416821229471899 88721539340125231844207849)
      ·
        refine ⟨66541154505093923883155887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88721539340125231844207849 66541154505093923883155887)
        ·
          refine ⟨99811731757640885824733831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66541154505093923883155887 99811731757640885824733831)
          ·
            refine ⟨149717597636461328737100747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99811731757640885824733831 149717597636461328737100747)
            ·
              refine ⟨224576396454691993105651121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149717597636461328737100747 224576396454691993105651121)
              ·
                refine ⟨168432297341018994829238341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224576396454691993105651121 168432297341018994829238341)
                ·
                  refine ⟨31581055751441061530482189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168432297341018994829238341 31581055751441061530482189)
                  ·
                    refine ⟨11842895906790398073930821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31581055751441061530482189 11842895906790398073930821)
                    ·
                      refine ⟨2220542982523199638862029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11842895906790398073930821 2220542982523199638862029)
                      ·
                        rfl

theorem cell23_4324492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_4324492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324492 prefixEnd_4324492 := by exact prefixLift 4324492
  have htrace : WordTrace (prefixWord ++ tailWord_4324492) baseStart_4324492 baseEnd_4324492 := by
    simpa [prefixWord, tailWord_4324492, baseEnd_4324492] using wordTrace_append hprefix tailTrace_4324492
  have hstable : (prefixWord ++ tailWord_4324492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324492).length < 2 ^ (prefixWord ++ tailWord_4324492).sum := by decide
  have hdescent : baseEnd_4324492 < baseStart_4324492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324503 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_4324503 : Nat := 118140960795 + 4324503 * 2 ^ 59
def prefixEnd_4324503 : Nat := 4983230072969 + 3 ^ 40 * 4324503 * 2
def baseEnd_4324503 : Nat := 2220548630810399095824479

theorem tailTrace_4324503 : CollatzResearch.WordTrace tailWord_4324503 prefixEnd_4324503 2220548630810399095824479 := by
  unfold tailWord_4324503
  simp only [CollatzResearch.WordTrace]
  refine ⟨157727582252071672157242163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105151721501381114771494775 157727582252071672157242163)
  ·
    refine ⟨236591373378107508235863245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157727582252071672157242163 236591373378107508235863245)
    ·
      refine ⟨88721765016790315588448717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236591373378107508235863245 88721765016790315588448717)
      ·
        refine ⟨33270661881296368345668269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88721765016790315588448717 33270661881296368345668269)
        ·
          refine ⟨12476498205486138129625601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33270661881296368345668269 12476498205486138129625601)
          ·
            refine ⟨9357373654114603597219201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12476498205486138129625601 9357373654114603597219201)
            ·
              refine ⟨7018030240585952697914401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9357373654114603597219201 7018030240585952697914401)
              ·
                refine ⟨5263522680439464523435801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7018030240585952697914401 5263522680439464523435801)
                ·
                  refine ⟨3947642010329598392576851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5263522680439464523435801 3947642010329598392576851)
                  ·
                    refine ⟨5921463015494397588865277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947642010329598392576851 5921463015494397588865277)
                    ·
                      refine ⟨2220548630810399095824479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921463015494397588865277 2220548630810399095824479)
                      ·
                        rfl

theorem cell23_4324503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_4324503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324503 prefixEnd_4324503 := by exact prefixLift 4324503
  have htrace : WordTrace (prefixWord ++ tailWord_4324503) baseStart_4324503 baseEnd_4324503 := by
    simpa [prefixWord, tailWord_4324503, baseEnd_4324503] using wordTrace_append hprefix tailTrace_4324503
  have hstable : (prefixWord ++ tailWord_4324503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324503).length < 2 ^ (prefixWord ++ tailWord_4324503).sum := by decide
  have hdescent : baseEnd_4324503 < baseStart_4324503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324519 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 8]
def baseStart_4324519 : Nat := 118140960795 + 4324519 * 2 ^ 59
def prefixEnd_4324519 : Nat := 4983230072969 + 3 ^ 40 * 4324519 * 2
def baseEnd_4324519 : Nat := 740185615500290344408135

theorem tailTrace_4324519 : CollatzResearch.WordTrace tailWord_4324519 prefixEnd_4324519 740185615500290344408135 := by
  unfold tailWord_4324519
  simp only [CollatzResearch.WordTrace]
  refine ⟨157728165820013706889824611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105152110546675804593216407 157728165820013706889824611)
  ·
    refine ⟨236592248730020560334736917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157728165820013706889824611 236592248730020560334736917)
    ·
      refine ⟨11090261659219713765690793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 236592248730020560334736917 11090261659219713765690793)
      ·
        refine ⟨8317696244414785324268095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11090261659219713765690793 8317696244414785324268095)
        ·
          refine ⟨12476544366622177986402143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8317696244414785324268095 12476544366622177986402143)
          ·
            refine ⟨18714816549933266979603215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12476544366622177986402143 18714816549933266979603215)
            ·
              refine ⟨28072224824899900469404823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18714816549933266979603215 28072224824899900469404823)
              ·
                refine ⟨42108337237349850704107235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28072224824899900469404823 42108337237349850704107235)
                ·
                  refine ⟨63162505856024776056160853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42108337237349850704107235 63162505856024776056160853)
                  ·
                    refine ⟨740185615500290344408135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63162505856024776056160853 740185615500290344408135)
                    ·
                      rfl

theorem cell23_4324519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_4324519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324519 prefixEnd_4324519 := by exact prefixLift 4324519
  have htrace : WordTrace (prefixWord ++ tailWord_4324519) baseStart_4324519 baseEnd_4324519 := by
    simpa [prefixWord, tailWord_4324519, baseEnd_4324519] using wordTrace_append hprefix tailTrace_4324519
  have hstable : (prefixWord ++ tailWord_4324519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324519).length < 2 ^ (prefixWord ++ tailWord_4324519).sum := by decide
  have hdescent : baseEnd_4324519 < baseStart_4324519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324660 : List Nat := [2, 5, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_4324660 : Nat := 118140960795 + 4324660 * 2 ^ 59
def prefixEnd_4324660 : Nat := 4983230072969 + 3 ^ 40 * 4324660 * 2
def baseEnd_4324660 : Nat := 740209749091051660520419

theorem tailTrace_4324660 : CollatzResearch.WordTrace tailWord_4324660 prefixEnd_4324660 740209749091051660520419 := by
  unfold tailWord_4324660
  simp only [CollatzResearch.WordTrace]
  refine ⟨78866654256251443985353717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105155539008335258647138289 78866654256251443985353717)
  ·
    refine ⟨7393748836523572873626911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78866654256251443985353717 7393748836523572873626911)
    ·
      refine ⟨11090623254785359310440367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7393748836523572873626911 11090623254785359310440367)
      ·
        refine ⟨16635934882178038965660551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11090623254785359310440367 16635934882178038965660551)
        ·
          refine ⟨24953902323267058448490827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16635934882178038965660551 24953902323267058448490827)
          ·
            refine ⟨37430853484900587672736241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24953902323267058448490827 37430853484900587672736241)
            ·
              refine ⟨28073140113675440754552181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37430853484900587672736241 28073140113675440754552181)
              ·
                refine ⟨2631856885657072570739267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28073140113675440754552181 2631856885657072570739267)
                ·
                  refine ⟨3947785328485608856108901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631856885657072570739267 3947785328485608856108901)
                  ·
                    refine ⟨740209749091051660520419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3947785328485608856108901 740209749091051660520419)
                    ·
                      rfl

theorem cell23_4324660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_4324660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324660 prefixEnd_4324660 := by exact prefixLift 4324660
  have htrace : WordTrace (prefixWord ++ tailWord_4324660) baseStart_4324660 baseEnd_4324660 := by
    simpa [prefixWord, tailWord_4324660, baseEnd_4324660] using wordTrace_append hprefix tailTrace_4324660
  have hstable : (prefixWord ++ tailWord_4324660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324660).length < 2 ^ (prefixWord ++ tailWord_4324660).sum := by decide
  have hdescent : baseEnd_4324660 < baseStart_4324660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324673 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 6]
def baseStart_4324673 : Nat := 118140960795 + 4324673 * 2 ^ 59
def prefixEnd_4324673 : Nat := 4983230072969 + 3 ^ 40 * 4324673 * 2
def baseEnd_4324673 : Nat := 246737324724629270077633

theorem tailTrace_4324673 : CollatzResearch.WordTrace tailWord_4324673 prefixEnd_4324673 246737324724629270077633 := by
  unfold tailWord_4324673
  simp only [CollatzResearch.WordTrace]
  refine ⟨157733782661455791190930673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105155855107637194127287115 157733782661455791190930673)
  ·
    refine ⟨118300336996091843393198005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157733782661455791190930673 118300336996091843393198005)
    ·
      refine ⟨11090656593383610318112313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118300336996091843393198005 11090656593383610318112313)
      ·
        refine ⟨8317992445037707738584235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11090656593383610318112313 8317992445037707738584235)
        ·
          refine ⟨12476988667556561607876353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8317992445037707738584235 12476988667556561607876353)
          ·
            refine ⟨9357741500667421205907265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12476988667556561607876353 9357741500667421205907265)
            ·
              refine ⟨7018306125500565904430449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9357741500667421205907265 7018306125500565904430449)
              ·
                refine ⟨5263729594125424428322837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7018306125500565904430449 5263729594125424428322837)
                ·
                  refine ⟨246737324724629270077633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5263729594125424428322837 246737324724629270077633)
                  ·
                    rfl

theorem cell23_4324673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 6].length) (baseStart_4324673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324673 prefixEnd_4324673 := by exact prefixLift 4324673
  have htrace : WordTrace (prefixWord ++ tailWord_4324673) baseStart_4324673 baseEnd_4324673 := by
    simpa [prefixWord, tailWord_4324673, baseEnd_4324673] using wordTrace_append hprefix tailTrace_4324673
  have hstable : (prefixWord ++ tailWord_4324673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324673).length < 2 ^ (prefixWord ++ tailWord_4324673).sum := by decide
  have hdescent : baseEnd_4324673 < baseStart_4324673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324694 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4324694 : Nat := 118140960795 + 4324694 * 2 ^ 59
def prefixEnd_4324694 : Nat := 4983230072969 + 3 ^ 40 * 4324694 * 2
def baseEnd_4324694 : Nat := 740215568538469282845367

theorem tailTrace_4324694 : CollatzResearch.WordTrace tailWord_4324694 prefixEnd_4324694 740215568538469282845367 := by
  unfold tailWord_4324694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9858409287148731986090321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105156365729586474518296757 9858409287148731986090321)
  ·
    refine ⟨7393806965361548989567741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9858409287148731986090321 7393806965361548989567741)
    ·
      refine ⟨2772677612010580871087903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7393806965361548989567741 2772677612010580871087903)
      ·
        refine ⟨4159016418015871306631855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772677612010580871087903 4159016418015871306631855)
        ·
          refine ⟨6238524627023806959947783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159016418015871306631855 6238524627023806959947783)
          ·
            refine ⟨9357786940535710439921675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238524627023806959947783 9357786940535710439921675)
            ·
              refine ⟨14036680410803565659882513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9357786940535710439921675 14036680410803565659882513)
              ·
                refine ⟨10527510308102674244911885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14036680410803565659882513 10527510308102674244911885)
                ·
                  refine ⟨3947816365538502841841957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10527510308102674244911885 3947816365538502841841957)
                  ·
                    refine ⟨740215568538469282845367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3947816365538502841841957 740215568538469282845367)
                    ·
                      rfl

theorem cell23_4324694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4324694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324694 prefixEnd_4324694 := by exact prefixLift 4324694
  have htrace : WordTrace (prefixWord ++ tailWord_4324694) baseStart_4324694 baseEnd_4324694 := by
    simpa [prefixWord, tailWord_4324694, baseEnd_4324694] using wordTrace_append hprefix tailTrace_4324694
  have hstable : (prefixWord ++ tailWord_4324694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324694).length < 2 ^ (prefixWord ++ tailWord_4324694).sum := by decide
  have hdescent : baseEnd_4324694 < baseStart_4324694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324716 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_4324716 : Nat := 118140960795 + 4324716 * 2 ^ 59
def prefixEnd_4324716 : Nat := 4983230072969 + 3 ^ 40 * 4324716 * 2
def baseEnd_4324716 : Nat := 740219334063268920820333

theorem tailTrace_4324716 : CollatzResearch.WordTrace tailWord_4324716 prefixEnd_4324716 740219334063268920820333 := by
  unfold tailWord_4324716
  simp only [CollatzResearch.WordTrace]
  refine ⟨78867675500150004767373001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105156900666866673023164001 78867675500150004767373001)
  ·
    refine ⟨59150756625112503575529751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78867675500150004767373001 59150756625112503575529751)
    ·
      refine ⟨88726134937668755363294627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59150756625112503575529751 88726134937668755363294627)
      ·
        refine ⟨133089202406503133044941941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88726134937668755363294627 133089202406503133044941941)
        ·
          refine ⟨12477112725609668722963307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133089202406503133044941941 12477112725609668722963307)
          ·
            refine ⟨18715669088414503084444961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12477112725609668722963307 18715669088414503084444961)
            ·
              refine ⟨14036751816310877313333721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18715669088414503084444961 14036751816310877313333721)
              ·
                refine ⟨10527563862233157985000291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14036751816310877313333721 10527563862233157985000291)
                ·
                  refine ⟨15791345793349736977500437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10527563862233157985000291 15791345793349736977500437)
                  ·
                    refine ⟨740219334063268920820333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15791345793349736977500437 740219334063268920820333)
                    ·
                      rfl

theorem cell23_4324716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_4324716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324716 prefixEnd_4324716 := by exact prefixLift 4324716
  have htrace : WordTrace (prefixWord ++ tailWord_4324716) baseStart_4324716 baseEnd_4324716 := by
    simpa [prefixWord, tailWord_4324716, baseEnd_4324716] using wordTrace_append hprefix tailTrace_4324716
  have hstable : (prefixWord ++ tailWord_4324716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324716).length < 2 ^ (prefixWord ++ tailWord_4324716).sum := by decide
  have hdescent : baseEnd_4324716 < baseStart_4324716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324717 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_4324717 : Nat := 118140960795 + 4324717 * 2 ^ 59
def prefixEnd_4324717 : Nat := 4983230072969 + 3 ^ 40 * 4324717 * 2
def baseEnd_4324717 : Nat := 2220658515670461258548495

theorem tailTrace_4324717 : CollatzResearch.WordTrace tailWord_4324717 prefixEnd_4324717 2220658515670461258548495 := by
  unfold tailWord_4324717
  simp only [CollatzResearch.WordTrace]
  refine ⟨157735387473296386705532405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105156924982197591137021603 157735387473296386705532405)
  ·
    refine ⟨14787692575621536253643663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157735387473296386705532405 14787692575621536253643663)
    ·
      refine ⟨22181538863432304380465495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14787692575621536253643663 22181538863432304380465495)
      ·
        refine ⟨33272308295148456570698243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22181538863432304380465495 33272308295148456570698243)
        ·
          refine ⟨49908462442722684856047365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33272308295148456570698243 49908462442722684856047365)
          ·
            refine ⟨9357836708010503410508881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49908462442722684856047365 9357836708010503410508881)
            ·
              refine ⟨7018377531007877557881661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9357836708010503410508881 7018377531007877557881661)
              ·
                refine ⟨2631891574127954084205623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7018377531007877557881661 2631891574127954084205623)
                ·
                  refine ⟨3947837361191931126308435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2631891574127954084205623 3947837361191931126308435)
                  ·
                    refine ⟨5921756041787896689462653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947837361191931126308435 5921756041787896689462653)
                    ·
                      refine ⟨2220658515670461258548495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921756041787896689462653 2220658515670461258548495)
                      ·
                        rfl

theorem cell23_4324717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_4324717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324717 prefixEnd_4324717 := by exact prefixLift 4324717
  have htrace : WordTrace (prefixWord ++ tailWord_4324717) baseStart_4324717 baseEnd_4324717 := by
    simpa [prefixWord, tailWord_4324717, baseEnd_4324717] using wordTrace_append hprefix tailTrace_4324717
  have hstable : (prefixWord ++ tailWord_4324717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324717).length < 2 ^ (prefixWord ++ tailWord_4324717).sum := by decide
  have hdescent : baseEnd_4324717 < baseStart_4324717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324734 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4324734 : Nat := 118140960795 + 4324734 * 2 ^ 59
def prefixEnd_4324734 : Nat := 4983230072969 + 3 ^ 40 * 4324734 * 2
def baseEnd_4324734 : Nat := 2220667244841587692035917

theorem tailTrace_4324734 : CollatzResearch.WordTrace tailWord_4324734 prefixEnd_4324734 2220667244841587692035917 := by
  unfold tailWord_4324734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19717000939279349826112657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105157338342823199072600837 19717000939279349826112657)
  ·
    refine ⟨14787750704459512369584493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19717000939279349826112657 14787750704459512369584493)
    ·
      refine ⟨5545406514172317138594185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14787750704459512369584493 5545406514172317138594185)
      ·
        refine ⟨4159054885629237853945639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5545406514172317138594185 4159054885629237853945639)
        ·
          refine ⟨6238582328443856780918459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159054885629237853945639 6238582328443856780918459)
          ·
            refine ⟨9357873492665785171377689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238582328443856780918459 9357873492665785171377689)
            ·
              refine ⟨7018405119499338878533267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9357873492665785171377689 7018405119499338878533267)
              ·
                refine ⟨10527607679249008317799901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7018405119499338878533267 10527607679249008317799901)
                ·
                  refine ⟨3947852879718378119174963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10527607679249008317799901 3947852879718378119174963)
                  ·
                    refine ⟨5921779319577567178762445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947852879718378119174963 5921779319577567178762445)
                    ·
                      refine ⟨2220667244841587692035917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921779319577567178762445 2220667244841587692035917)
                      ·
                        rfl

theorem cell23_4324734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4324734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324734 prefixEnd_4324734 := by exact prefixLift 4324734
  have htrace : WordTrace (prefixWord ++ tailWord_4324734) baseStart_4324734 baseEnd_4324734 := by
    simpa [prefixWord, tailWord_4324734, baseEnd_4324734] using wordTrace_append hprefix tailTrace_4324734
  have hstable : (prefixWord ++ tailWord_4324734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324734).length < 2 ^ (prefixWord ++ tailWord_4324734).sum := by decide
  have hdescent : baseEnd_4324734 < baseStart_4324734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324740 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_4324740 : Nat := 118140960795 + 4324740 * 2 ^ 59
def prefixEnd_4324740 : Nat := 4983230072969 + 3 ^ 40 * 4324740 * 2
def baseEnd_4324740 : Nat := 2220670325725514668560889

theorem tailTrace_4324740 : CollatzResearch.WordTrace tailWord_4324740 prefixEnd_4324740 2220670325725514668560889 := by
  unfold tailWord_4324740
  simp only [CollatzResearch.WordTrace]
  refine ⟨78868113176106530816809837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105157484234808707755746449 78868113176106530816809837)
  ·
    refine ⟨29575542441039949056303689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78868113176106530816809837 29575542441039949056303689)
    ·
      refine ⟨22181656830779961792227767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29575542441039949056303689 22181656830779961792227767)
      ·
        refine ⟨33272485246169942688341651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22181656830779961792227767 33272485246169942688341651)
        ·
          refine ⟨49908727869254914032512477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33272485246169942688341651 49908727869254914032512477)
          ·
            refine ⟨18715772950970592762192179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49908727869254914032512477 18715772950970592762192179)
            ·
              refine ⟨28073659426455889143288269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18715772950970592762192179 28073659426455889143288269)
              ·
                refine ⟨10527622284920958428733101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28073659426455889143288269 10527622284920958428733101)
                ·
                  refine ⟨3947858356845359410774913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10527622284920958428733101 3947858356845359410774913)
                  ·
                    refine ⟨2960893767634019558081185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3947858356845359410774913 2960893767634019558081185)
                    ·
                      refine ⟨2220670325725514668560889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960893767634019558081185 2220670325725514668560889)
                      ·
                        rfl

theorem cell23_4324740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_4324740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324740 prefixEnd_4324740 := by exact prefixLift 4324740
  have htrace : WordTrace (prefixWord ++ tailWord_4324740) baseStart_4324740 baseEnd_4324740 := by
    simpa [prefixWord, tailWord_4324740, baseEnd_4324740] using wordTrace_append hprefix tailTrace_4324740
  have hstable : (prefixWord ++ tailWord_4324740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324740).length < 2 ^ (prefixWord ++ tailWord_4324740).sum := by decide
  have hdescent : baseEnd_4324740 < baseStart_4324740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324750 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_4324750 : Nat := 118140960795 + 4324750 * 2 ^ 59
def prefixEnd_4324750 : Nat := 4983230072969 + 3 ^ 40 * 4324750 * 2
def baseEnd_4324750 : Nat := 740225153510686543145281

theorem tailTrace_4324750 : CollatzResearch.WordTrace tailWord_4324750 prefixEnd_4324750 740225153510686543145281 := by
  unfold tailWord_4324750
  simp only [CollatzResearch.WordTrace]
  refine ⟨19717073885272104167685463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105157727388117888894322469 19717073885272104167685463)
  ·
    refine ⟨29575610827908156251528195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19717073885272104167685463 29575610827908156251528195)
    ·
      refine ⟨44363416241862234377292293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29575610827908156251528195 44363416241862234377292293)
      ·
        refine ⟨8318140545349168945742305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44363416241862234377292293 8318140545349168945742305)
        ·
          refine ⟨6238605409011876709306729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8318140545349168945742305 6238605409011876709306729)
          ·
            refine ⟨4678954056758907531980047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6238605409011876709306729 4678954056758907531980047)
            ·
              refine ⟨7018431085138361297970071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4678954056758907531980047 7018431085138361297970071)
              ·
                refine ⟨10527646627707541946955107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7018431085138361297970071 10527646627707541946955107)
                ·
                  refine ⟨15791469941561312920432661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10527646627707541946955107 15791469941561312920432661)
                  ·
                    refine ⟨740225153510686543145281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15791469941561312920432661 740225153510686543145281)
                    ·
                      rfl

theorem cell23_4324750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_4324750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324750 prefixEnd_4324750 := by exact prefixLift 4324750
  have htrace : WordTrace (prefixWord ++ tailWord_4324750) baseStart_4324750 baseEnd_4324750 := by
    simpa [prefixWord, tailWord_4324750, baseEnd_4324750] using wordTrace_append hprefix tailTrace_4324750
  have hstable : (prefixWord ++ tailWord_4324750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324750).length < 2 ^ (prefixWord ++ tailWord_4324750).sum := by decide
  have hdescent : baseEnd_4324750 < baseStart_4324750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324816 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_4324816 : Nat := 118140960795 + 4324816 * 2 ^ 59
def prefixEnd_4324816 : Nat := 4983230072969 + 3 ^ 40 * 4324816 * 2
def baseEnd_4324816 : Nat := 2220709350255256371210539

theorem tailTrace_4324816 : CollatzResearch.WordTrace tailWord_4324816 prefixEnd_4324816 2220709350255256371210539 := by
  unfold tailWord_4324816
  simp only [CollatzResearch.WordTrace]
  refine ⟨78869499149968863306693151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105159332199958484408924201 78869499149968863306693151)
  ·
    refine ⟨118304248724953294960039727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78869499149968863306693151 118304248724953294960039727)
    ·
      refine ⟨177456373087429942440059591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118304248724953294960039727 177456373087429942440059591)
      ·
        refine ⟨266184559631144913660089387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177456373087429942440059591 266184559631144913660089387)
        ·
          refine ⟨399276839446717370490134081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266184559631144913660089387 399276839446717370490134081)
          ·
            refine ⟨299457629585038027867600561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399276839446717370490134081 299457629585038027867600561)
            ·
              refine ⟨224593222188778520900700421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299457629585038027867600561 224593222188778520900700421)
              ·
                refine ⟨42111229160395972668881329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224593222188778520900700421 42111229160395972668881329)
                ·
                  refine ⟨31583421870296979501660997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42111229160395972668881329 31583421870296979501660997)
                  ·
                    refine ⟨5921891600680683656561437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31583421870296979501660997 5921891600680683656561437)
                    ·
                      refine ⟨2220709350255256371210539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5921891600680683656561437 2220709350255256371210539)
                      ·
                        rfl

theorem cell23_4324816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_4324816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324816 prefixEnd_4324816 := by exact prefixLift 4324816
  have htrace : WordTrace (prefixWord ++ tailWord_4324816) baseStart_4324816 baseEnd_4324816 := by
    simpa [prefixWord, tailWord_4324816, baseEnd_4324816] using wordTrace_append hprefix tailTrace_4324816
  have hstable : (prefixWord ++ tailWord_4324816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324816).length < 2 ^ (prefixWord ++ tailWord_4324816).sum := by decide
  have hdescent : baseEnd_4324816 < baseStart_4324816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324873 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 2, 5, 2]
def baseStart_4324873 : Nat := 118140960795 + 4324873 * 2 ^ 59
def prefixEnd_4324873 : Nat := 4983230072969 + 3 ^ 40 * 4324873 * 2
def baseEnd_4324873 : Nat := 2220738618652562648197777

theorem tailTrace_4324873 : CollatzResearch.WordTrace tailWord_4324873 prefixEnd_4324873 2220738618652562648197777 := by
  unfold tailWord_4324873
  simp only [CollatzResearch.WordTrace]
  refine ⟨157741077260731225348211273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105160718173820816898807515 157741077260731225348211273)
  ·
    refine ⟨118305807945548419011158455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157741077260731225348211273 118305807945548419011158455)
    ·
      refine ⟨177458711918322628516737683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118305807945548419011158455 177458711918322628516737683)
      ·
        refine ⟨266188067877483942775106525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177458711918322628516737683 266188067877483942775106525)
        ·
          refine ⟨99820525454056478540664947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266188067877483942775106525 99820525454056478540664947)
          ·
            refine ⟨149730788181084717810997421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99820525454056478540664947 149730788181084717810997421)
            ·
              refine ⟨56149045567906769179124033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149730788181084717810997421 56149045567906769179124033)
              ·
                refine ⟨42111784175930076884343025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56149045567906769179124033 42111784175930076884343025)
                ·
                  refine ⟨31583838131947557663257269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42111784175930076884343025 31583838131947557663257269)
                  ·
                    refine ⟨2960984824870083530930369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31583838131947557663257269 2960984824870083530930369)
                    ·
                      refine ⟨2220738618652562648197777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2960984824870083530930369 2220738618652562648197777)
                      ·
                        rfl

theorem cell23_4324873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 5, 2].length) (baseStart_4324873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324873 prefixEnd_4324873 := by exact prefixLift 4324873
  have htrace : WordTrace (prefixWord ++ tailWord_4324873) baseStart_4324873 baseEnd_4324873 := by
    simpa [prefixWord, tailWord_4324873, baseEnd_4324873] using wordTrace_append hprefix tailTrace_4324873
  have hstable : (prefixWord ++ tailWord_4324873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324873).length < 2 ^ (prefixWord ++ tailWord_4324873).sum := by decide
  have hdescent : baseEnd_4324873 < baseStart_4324873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324883 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 2, 5]
def baseStart_4324883 : Nat := 118140960795 + 4324883 * 2 ^ 59
def prefixEnd_4324883 : Nat := 4983230072969 + 3 ^ 40 * 4324883 * 2
def baseEnd_4324883 : Nat := 740247917819702536357577

theorem tailTrace_4324883 : CollatzResearch.WordTrace tailWord_4324883 prefixEnd_4324883 740247917819702536357577 := by
  unfold tailWord_4324883
  simp only [CollatzResearch.WordTrace]
  refine ⟨157741441990694997056075303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105160961327129998037383535 157741441990694997056075303)
  ·
    refine ⟨236612162986042495584112955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157741441990694997056075303 236612162986042495584112955)
    ·
      refine ⟨354918244479063743376169433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236612162986042495584112955 354918244479063743376169433)
      ·
        refine ⟨266188683359297807532127075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354918244479063743376169433 266188683359297807532127075)
        ·
          refine ⟨399283025038946711298190613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266188683359297807532127075 399283025038946711298190613)
          ·
            refine ⟨18716391798700627092102685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 399283025038946711298190613 18716391798700627092102685)
            ·
              refine ⟨7018646924512735159538507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18716391798700627092102685 7018646924512735159538507)
              ·
                refine ⟨10527970386769102739307761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7018646924512735159538507 10527970386769102739307761)
                ·
                  refine ⟨7895977790076827054480821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10527970386769102739307761 7895977790076827054480821)
                  ·
                    refine ⟨740247917819702536357577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7895977790076827054480821 740247917819702536357577)
                    ·
                      rfl

theorem cell23_4324883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 5].length) (baseStart_4324883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324883 prefixEnd_4324883 := by exact prefixLift 4324883
  have htrace : WordTrace (prefixWord ++ tailWord_4324883) baseStart_4324883 baseEnd_4324883 := by
    simpa [prefixWord, tailWord_4324883, baseEnd_4324883] using wordTrace_append hprefix tailTrace_4324883
  have hstable : (prefixWord ++ tailWord_4324883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324883).length < 2 ^ (prefixWord ++ tailWord_4324883).sum := by decide
  have hdescent : baseEnd_4324883 < baseStart_4324883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324920 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 2, 4, 2]
def baseStart_4324920 : Nat := 118140960795 + 4324920 * 2 ^ 59
def prefixEnd_4324920 : Nat := 4983230072969 + 3 ^ 40 * 4324920 * 2
def baseEnd_4324920 : Nat := 2220762752243323964310061

theorem tailTrace_4324920 : CollatzResearch.WordTrace tailWord_4324920 prefixEnd_4324920 2220762752243323964310061 := by
  unfold tailWord_4324920
  simp only [CollatzResearch.WordTrace]
  refine ⟨78871395745780476187586107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105161860994373968250114809 78871395745780476187586107)
  ·
    refine ⟨118307093618670714281379161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78871395745780476187586107 118307093618670714281379161)
    ·
      refine ⟨88730320214003035711034371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118307093618670714281379161 88730320214003035711034371)
      ·
        refine ⟨133095480321004553566551557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88730320214003035711034371 133095480321004553566551557)
        ·
          refine ⟨24955402560188353793728417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133095480321004553566551557 24955402560188353793728417)
          ·
            refine ⟨18716551920141265345296313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24955402560188353793728417 18716551920141265345296313)
            ·
              refine ⟨14037413940105949008972235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18716551920141265345296313 14037413940105949008972235)
              ·
                refine ⟨21056120910158923513458353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14037413940105949008972235 21056120910158923513458353)
                ·
                  refine ⟨15792090682619192635093765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21056120910158923513458353 15792090682619192635093765)
                  ·
                    refine ⟨2961017002991098619080081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15792090682619192635093765 2961017002991098619080081)
                    ·
                      refine ⟨2220762752243323964310061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961017002991098619080081 2220762752243323964310061)
                      ·
                        rfl

theorem cell23_4324920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_4324920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324920 prefixEnd_4324920 := by exact prefixLift 4324920
  have htrace : WordTrace (prefixWord ++ tailWord_4324920) baseStart_4324920 baseEnd_4324920 := by
    simpa [prefixWord, tailWord_4324920, baseEnd_4324920] using wordTrace_append hprefix tailTrace_4324920
  have hstable : (prefixWord ++ tailWord_4324920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324920).length < 2 ^ (prefixWord ++ tailWord_4324920).sum := by decide
  have hdescent : baseEnd_4324920 < baseStart_4324920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324936 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_4324936 : Nat := 118140960795 + 4324936 * 2 ^ 59
def prefixEnd_4324936 : Nat := 4983230072969 + 3 ^ 40 * 4324936 * 2
def baseEnd_4324936 : Nat := 2220770967933795901709987

theorem tailTrace_4324936 : CollatzResearch.WordTrace tailWord_4324936 prefixEnd_4324936 2220770967933795901709987 := by
  unfold tailWord_4324936
  simp only [CollatzResearch.WordTrace]
  refine ⟨78871687529751493553877331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105162250039668658071836441 78871687529751493553877331)
  ·
    refine ⟨118307531294627240330815997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78871687529751493553877331 118307531294627240330815997)
    ·
      refine ⟨44365324235485215124055999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118307531294627240330815997 44365324235485215124055999)
      ·
        refine ⟨66547986353227822686083999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44365324235485215124055999 66547986353227822686083999)
        ·
          refine ⟨99821979529841734029125999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66547986353227822686083999 99821979529841734029125999)
          ·
            refine ⟨149732969294762601043688999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99821979529841734029125999 149732969294762601043688999)
            ·
              refine ⟨224599453942143901565533499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149732969294762601043688999 224599453942143901565533499)
              ·
                refine ⟨336899180913215852348300249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224599453942143901565533499 336899180913215852348300249)
                ·
                  refine ⟨252674385684911889261225187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 336899180913215852348300249 252674385684911889261225187)
                  ·
                    refine ⟨379011578527367833891837781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252674385684911889261225187 379011578527367833891837781)
                    ·
                      refine ⟨2220770967933795901709987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 379011578527367833891837781 2220770967933795901709987)
                      ·
                        rfl

theorem cell23_4324936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_4324936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324936 prefixEnd_4324936 := by exact prefixLift 4324936
  have htrace : WordTrace (prefixWord ++ tailWord_4324936) baseStart_4324936 baseEnd_4324936 := by
    simpa [prefixWord, tailWord_4324936, baseEnd_4324936] using wordTrace_append hprefix tailTrace_4324936
  have hstable : (prefixWord ++ tailWord_4324936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324936).length < 2 ^ (prefixWord ++ tailWord_4324936).sum := by decide
  have hdescent : baseEnd_4324936 < baseStart_4324936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324964 : List Nat := [2, 3, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_4324964 : Nat := 118140960795 + 4324964 * 2 ^ 59
def prefixEnd_4324964 : Nat := 4983230072969 + 3 ^ 40 * 4324964 * 2
def baseEnd_4324964 : Nat := 740261781797373930719953

theorem tailTrace_4324964 : CollatzResearch.WordTrace tailWord_4324964 prefixEnd_4324964 740261781797373930719953 := by
  unfold tailWord_4324964
  simp only [CollatzResearch.WordTrace]
  refine ⟨78872198151700773944886973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105162930868934365259849297 78872198151700773944886973)
  ·
    refine ⟨29577074306887790229332615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78872198151700773944886973 29577074306887790229332615)
    ·
      refine ⟨44365611460331685343998923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29577074306887790229332615 44365611460331685343998923)
      ·
        refine ⟨66548417190497528015998385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44365611460331685343998923 66548417190497528015998385)
        ·
          refine ⟨49911312892873146011998789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66548417190497528015998385 49911312892873146011998789)
          ·
            refine ⟨9358371167413714877249773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49911312892873146011998789 9358371167413714877249773)
            ·
              refine ⟨3509389187780143078968665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9358371167413714877249773 3509389187780143078968665)
              ·
                refine ⟨2632041890835107309226499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509389187780143078968665 2632041890835107309226499)
                ·
                  refine ⟨3948062836252660963839749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632041890835107309226499 3948062836252660963839749)
                  ·
                    refine ⟨740261781797373930719953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948062836252660963839749 740261781797373930719953)
                    ·
                      rfl

theorem cell23_4324964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_4324964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324964 prefixEnd_4324964 := by exact prefixLift 4324964
  have htrace : WordTrace (prefixWord ++ tailWord_4324964) baseStart_4324964 baseEnd_4324964 := by
    simpa [prefixWord, tailWord_4324964, baseEnd_4324964] using wordTrace_append hprefix tailTrace_4324964
  have hstable : (prefixWord ++ tailWord_4324964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324964).length < 2 ^ (prefixWord ++ tailWord_4324964).sum := by decide
  have hdescent : baseEnd_4324964 < baseStart_4324964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4324997 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 2, 3, 2]
def baseStart_4324997 : Nat := 118140960795 + 4324997 * 2 ^ 59
def prefixEnd_4324997 : Nat := 4983230072969 + 3 ^ 40 * 4324997 * 2
def baseEnd_4324997 : Nat := 2220802290253720163047207

theorem tailTrace_4324997 : CollatzResearch.WordTrace tailWord_4324997 prefixEnd_4324997 2220802290253720163047207 := by
  unfold tailWord_4324997
  simp only [CollatzResearch.WordTrace]
  refine ⟨157745599912281994525725245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105163733274854663017150163 157745599912281994525725245)
  ·
    refine ⟨59154599967105747947146967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157745599912281994525725245 59154599967105747947146967)
    ·
      refine ⟨88731899950658621920720451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59154599967105747947146967 88731899950658621920720451)
      ·
        refine ⟨133097849925987932881080677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88731899950658621920720451 133097849925987932881080677)
        ·
          refine ⟨24955846861122737415202627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133097849925987932881080677 24955846861122737415202627)
          ·
            refine ⟨37433770291684106122803941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24955846861122737415202627 37433770291684106122803941)
            ·
              refine ⟨7018831929690769898025739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37433770291684106122803941 7018831929690769898025739)
              ·
                refine ⟨10528247894536154847038609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7018831929690769898025739 10528247894536154847038609)
                ·
                  refine ⟨7896185920902116135278957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10528247894536154847038609 7896185920902116135278957)
                  ·
                    refine ⟨2961069720338293550729609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7896185920902116135278957 2961069720338293550729609)
                    ·
                      refine ⟨2220802290253720163047207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961069720338293550729609 2220802290253720163047207)
                      ·
                        rfl

theorem cell23_4324997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_4324997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4324997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4324997 prefixEnd_4324997 := by exact prefixLift 4324997
  have htrace : WordTrace (prefixWord ++ tailWord_4324997) baseStart_4324997 baseEnd_4324997 := by
    simpa [prefixWord, tailWord_4324997, baseEnd_4324997] using wordTrace_append hprefix tailTrace_4324997
  have hstable : (prefixWord ++ tailWord_4324997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4324997).length < 2 ^ (prefixWord ++ tailWord_4324997).sum := by decide
  have hdescent : baseEnd_4324997 < baseStart_4324997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4324997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325003 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 1, 6]
def baseStart_4325003 : Nat := 118140960795 + 4325003 * 2 ^ 59
def prefixEnd_4325003 : Nat := 4983230072969 + 3 ^ 40 * 4325003 * 2
def baseEnd_4325003 : Nat := 740268457045882379857393

theorem tailTrace_4325003 : CollatzResearch.WordTrace tailWord_4325003 prefixEnd_4325003 740268457045882379857393 := by
  unfold tailWord_4325003
  simp only [CollatzResearch.WordTrace]
  refine ⟨157745818750260257550443663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105163879166840171700295775 157745818750260257550443663)
  ·
    refine ⟨236618728125390386325665495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157745818750260257550443663 236618728125390386325665495)
    ·
      refine ⟨354928092188085579488498243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236618728125390386325665495 354928092188085579488498243)
      ·
        refine ⟨532392138282128369232747365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354928092188085579488498243 532392138282128369232747365)
        ·
          refine ⟨99823525927899069231140131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 532392138282128369232747365 99823525927899069231140131)
          ·
            refine ⟨149735288891848603846710197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99823525927899069231140131 149735288891848603846710197)
            ·
              refine ⟨14037683333610806610629081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149735288891848603846710197 14037683333610806610629081)
              ·
                refine ⟨10528262500208104957971811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14037683333610806610629081 10528262500208104957971811)
                ·
                  refine ⟨15792393750312157436957717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10528262500208104957971811 15792393750312157436957717)
                  ·
                    refine ⟨740268457045882379857393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15792393750312157436957717 740268457045882379857393)
                    ·
                      rfl

theorem cell23_4325003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 6].length) (baseStart_4325003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325003 prefixEnd_4325003 := by exact prefixLift 4325003
  have htrace : WordTrace (prefixWord ++ tailWord_4325003) baseStart_4325003 baseEnd_4325003 := by
    simpa [prefixWord, tailWord_4325003, baseEnd_4325003] using wordTrace_append hprefix tailTrace_4325003
  have hstable : (prefixWord ++ tailWord_4325003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325003).length < 2 ^ (prefixWord ++ tailWord_4325003).sum := by decide
  have hdescent : baseEnd_4325003 < baseStart_4325003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325027 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 3, 2, 2]
def baseStart_4325027 : Nat := 118140960795 + 4325027 * 2 ^ 59
def prefixEnd_4325027 : Nat := 4983230072969 + 3 ^ 40 * 4325027 * 2
def baseEnd_4325027 : Nat := 2220817694673355045672069

theorem tailTrace_4325027 : CollatzResearch.WordTrace tailWord_4325027 prefixEnd_4325027 2220817694673355045672069 := by
  unfold tailWord_4325027
  simp only [CollatzResearch.WordTrace]
  refine ⟨157746694102173309649317335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105164462734782206432878223 157746694102173309649317335)
  ·
    refine ⟨236620041153259964473976003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157746694102173309649317335 236620041153259964473976003)
    ·
      refine ⟨354930061729889946710964005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236620041153259964473976003 354930061729889946710964005)
      ·
        refine ⟨66549386574354365008305751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354930061729889946710964005 66549386574354365008305751)
        ·
          refine ⟨99824079861531547512458627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66549386574354365008305751 99824079861531547512458627)
          ·
            refine ⟨149736119792297321268687941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99824079861531547512458627 149736119792297321268687941)
            ·
              refine ⟨28075522461055747737878989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149736119792297321268687941 28075522461055747737878989)
              ·
                refine ⟨10528320922895905401704621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28075522461055747737878989 10528320922895905401704621)
                ·
                  refine ⟨3948120346085964525639233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10528320922895905401704621 3948120346085964525639233)
                  ·
                    refine ⟨2961090259564473394229425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948120346085964525639233 2961090259564473394229425)
                    ·
                      refine ⟨2220817694673355045672069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961090259564473394229425 2220817694673355045672069)
                      ·
                        rfl

theorem cell23_4325027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_4325027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325027 prefixEnd_4325027 := by exact prefixLift 4325027
  have htrace : WordTrace (prefixWord ++ tailWord_4325027) baseStart_4325027 baseEnd_4325027 := by
    simpa [prefixWord, tailWord_4325027, baseEnd_4325027] using wordTrace_append hprefix tailTrace_4325027
  have hstable : (prefixWord ++ tailWord_4325027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325027).length < 2 ^ (prefixWord ++ tailWord_4325027).sum := by decide
  have hdescent : baseEnd_4325027 < baseStart_4325027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325037 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4325037 : Nat := 118140960795 + 4325037 * 2 ^ 59
def prefixEnd_4325037 : Nat := 4983230072969 + 3 ^ 40 * 4325037 * 2
def baseEnd_4325037 : Nat := 740274276493300002182341

theorem tailTrace_4325037 : CollatzResearch.WordTrace tailWord_4325037 prefixEnd_4325037 740274276493300002182341 := by
  unfold tailWord_4325037
  simp only [CollatzResearch.WordTrace]
  refine ⟨157747058832137081357181365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105164705888091387571454243 157747058832137081357181365)
  ·
    refine ⟨14788786765512851377235753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157747058832137081357181365 14788786765512851377235753)
    ·
      refine ⟨11091590074134638532926815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14788786765512851377235753 11091590074134638532926815)
      ·
        refine ⟨16637385111201957799390223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11091590074134638532926815 16637385111201957799390223)
        ·
          refine ⟨24956077666802936699085335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16637385111201957799390223 24956077666802936699085335)
          ·
            refine ⟨37434116500204405048628003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24956077666802936699085335 37434116500204405048628003)
            ·
              refine ⟨56151174750306607572942005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37434116500204405048628003 56151174750306607572942005)
              ·
                refine ⟨5264172632841244459963313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56151174750306607572942005 5264172632841244459963313)
                ·
                  refine ⟨3948129474630933344972485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5264172632841244459963313 3948129474630933344972485)
                  ·
                    refine ⟨740274276493300002182341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948129474630933344972485 740274276493300002182341)
                    ·
                      rfl

theorem cell23_4325037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4325037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325037 prefixEnd_4325037 := by exact prefixLift 4325037
  have htrace : WordTrace (prefixWord ++ tailWord_4325037) baseStart_4325037 baseEnd_4325037 := by
    simpa [prefixWord, tailWord_4325037, baseEnd_4325037] using wordTrace_append hprefix tailTrace_4325037
  have hstable : (prefixWord ++ tailWord_4325037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325037).length < 2 ^ (prefixWord ++ tailWord_4325037).sum := by decide
  have hdescent : baseEnd_4325037 < baseStart_4325037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325050 : List Nat := [3, 1, 1, 1, 2, 5, 3, 7]
def baseStart_4325050 : Nat := 118140960795 + 4325050 * 2 ^ 59
def prefixEnd_4325050 : Nat := 4983230072969 + 3 ^ 40 * 4325050 * 2
def baseEnd_4325050 : Nat := 82252944619570683543869

theorem tailTrace_4325050 : CollatzResearch.WordTrace tailWord_4325050 prefixEnd_4325050 82252944619570683543869 := by
  unfold tailWord_4325050
  simp only [CollatzResearch.WordTrace]
  refine ⟨39436883245272496144351151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105165021987393323051603069 39436883245272496144351151)
  ·
    refine ⟨59155324867908744216526727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39436883245272496144351151 59155324867908744216526727)
    ·
      refine ⟨88732987301863116324790091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59155324867908744216526727 88732987301863116324790091)
      ·
        refine ⟨133099480952794674487185137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88732987301863116324790091 133099480952794674487185137)
        ·
          refine ⟨99824610714596005865388853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133099480952794674487185137 99824610714596005865388853)
          ·
            refine ⟨9358557254493375549880205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99824610714596005865388853 9358557254493375549880205)
            ·
              refine ⟨3509458970435015831205077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9358557254493375549880205 3509458970435015831205077)
              ·
                refine ⟨82252944619570683543869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3509458970435015831205077 82252944619570683543869)
                ·
                  rfl

theorem cell23_4325050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_4325050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325050 prefixEnd_4325050 := by exact prefixLift 4325050
  have htrace : WordTrace (prefixWord ++ tailWord_4325050) baseStart_4325050 baseEnd_4325050 := by
    simpa [prefixWord, tailWord_4325050, baseEnd_4325050] using wordTrace_append hprefix tailTrace_4325050
  have hstable : (prefixWord ++ tailWord_4325050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325050).length < 2 ^ (prefixWord ++ tailWord_4325050).sum := by decide
  have hdescent : baseEnd_4325050 < baseStart_4325050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325123 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 9]
def baseStart_4325123 : Nat := 118140960795 + 4325123 * 2 ^ 59
def prefixEnd_4325123 : Nat := 4983230072969 + 3 ^ 40 * 4325123 * 2
def baseEnd_4325123 : Nat := 246762998757354074452403

theorem tailTrace_4325123 : CollatzResearch.WordTrace tailWord_4325123 prefixEnd_4325123 246762998757354074452403 := by
  unfold tailWord_4325123
  simp only [CollatzResearch.WordTrace]
  refine ⟨157750195509825518044812023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105166797006550345363208015 157750195509825518044812023)
  ·
    refine ⟨236625293264738277067218035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157750195509825518044812023 236625293264738277067218035)
    ·
      refine ⟨354937939897107415600827053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236625293264738277067218035 354937939897107415600827053)
      ·
        refine ⟨133101727461415280850310145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354937939897107415600827053 133101727461415280850310145)
        ·
          refine ⟨99826295596061460637732609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133101727461415280850310145 99826295596061460637732609)
          ·
            refine ⟨74869721697046095478299457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99826295596061460637732609 74869721697046095478299457)
            ·
              refine ⟨56152291272784571608724593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74869721697046095478299457 56152291272784571608724593)
              ·
                refine ⟨42114218454588428706543445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56152291272784571608724593 42114218454588428706543445)
                ·
                  refine ⟨246762998757354074452403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42114218454588428706543445 246762998757354074452403)
                  ·
                    rfl

theorem cell23_4325123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 9].length) (baseStart_4325123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325123 prefixEnd_4325123 := by exact prefixLift 4325123
  have htrace : WordTrace (prefixWord ++ tailWord_4325123) baseStart_4325123 baseEnd_4325123 := by
    simpa [prefixWord, tailWord_4325123, baseEnd_4325123] using wordTrace_append hprefix tailTrace_4325123
  have hstable : (prefixWord ++ tailWord_4325123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325123).length < 2 ^ (prefixWord ++ tailWord_4325123).sum := by decide
  have hdescent : baseEnd_4325123 < baseStart_4325123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325134 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4325134 : Nat := 118140960795 + 4325134 * 2 ^ 59
def prefixEnd_4325134 : Nat := 4983230072969 + 3 ^ 40 * 4325134 * 2
def baseEnd_4325134 : Nat := 2220872637103386127034077

theorem tailTrace_4325134 : CollatzResearch.WordTrace tailWord_4325134 prefixEnd_4325134 2220872637103386127034077 := by
  unfold tailWord_4325134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19718824589098208365432807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105167064475190444615641637 19718824589098208365432807)
  ·
    refine ⟨29578236883647312548149211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19718824589098208365432807 29578236883647312548149211)
    ·
      refine ⟨44367355325470968822223817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29578236883647312548149211 44367355325470968822223817)
      ·
        refine ⟨33275516494103226616667863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44367355325470968822223817 33275516494103226616667863)
        ·
          refine ⟨49913274741154839925001795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33275516494103226616667863 49913274741154839925001795)
          ·
            refine ⟨74869912111732259887502693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49913274741154839925001795 74869912111732259887502693)
            ·
              refine ⟨14038108520949798728906755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74869912111732259887502693 14038108520949798728906755)
              ·
                refine ⟨21057162781424698093360133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14038108520949798728906755 21057162781424698093360133)
                ·
                  refine ⟨3948218021517130892505025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21057162781424698093360133 3948218021517130892505025)
                  ·
                    refine ⟨2961163516137848169378769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948218021517130892505025 2961163516137848169378769)
                    ·
                      refine ⟨2220872637103386127034077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961163516137848169378769 2220872637103386127034077)
                      ·
                        rfl

theorem cell23_4325134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4325134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325134 prefixEnd_4325134 := by exact prefixLift 4325134
  have htrace : WordTrace (prefixWord ++ tailWord_4325134) baseStart_4325134 baseEnd_4325134 := by
    simpa [prefixWord, tailWord_4325134, baseEnd_4325134] using wordTrace_append hprefix tailTrace_4325134
  have hstable : (prefixWord ++ tailWord_4325134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325134).length < 2 ^ (prefixWord ++ tailWord_4325134).sum := by decide
  have hdescent : baseEnd_4325134 < baseStart_4325134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325180 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_4325180 : Nat := 118140960795 + 4325180 * 2 ^ 59
def prefixEnd_4325180 : Nat := 4983230072969 + 3 ^ 40 * 4325180 * 2
def baseEnd_4325180 : Nat := 2220896257213492947058865

theorem tailTrace_4325180 : CollatzResearch.WordTrace tailWord_4325180 prefixEnd_4325180 2220896257213492947058865 := by
  unfold tailWord_4325180
  simp only [CollatzResearch.WordTrace]
  refine ⟨78876137235309508389818497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105168182980412677853091329 78876137235309508389818497)
  ·
    refine ⟨59157102926482131292363873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78876137235309508389818497 59157102926482131292363873)
    ·
      refine ⟨44367827194861598469272905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59157102926482131292363873 44367827194861598469272905)
      ·
        refine ⟨33275870396146198851954679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44367827194861598469272905 33275870396146198851954679)
        ·
          refine ⟨49913805594219298277932019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33275870396146198851954679 49913805594219298277932019)
          ·
            refine ⟨74870708391328947416898029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49913805594219298277932019 74870708391328947416898029)
            ·
              refine ⟨28076515646748355281336761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74870708391328947416898029 28076515646748355281336761)
              ·
                refine ⟨21057386735061266461002571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28076515646748355281336761 21057386735061266461002571)
                ·
                  refine ⟨31586080102591899691503857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21057386735061266461002571 31586080102591899691503857)
                  ·
                    refine ⟨23689560076943924768627893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31586080102591899691503857 23689560076943924768627893)
                    ·
                      refine ⟨2220896257213492947058865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23689560076943924768627893 2220896257213492947058865)
                      ·
                        rfl

theorem cell23_4325180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_4325180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325180 prefixEnd_4325180 := by exact prefixLift 4325180
  have htrace : WordTrace (prefixWord ++ tailWord_4325180) baseStart_4325180 baseEnd_4325180 := by
    simpa [prefixWord, tailWord_4325180, baseEnd_4325180] using wordTrace_append hprefix tailTrace_4325180
  have hstable : (prefixWord ++ tailWord_4325180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325180).length < 2 ^ (prefixWord ++ tailWord_4325180).sum := by decide
  have hdescent : baseEnd_4325180 < baseStart_4325180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325217 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 3, 4]
def baseStart_4325217 : Nat := 118140960795 + 4325217 * 2 ^ 59
def prefixEnd_4325217 : Nat := 4983230072969 + 3 ^ 40 * 4325217 * 2
def baseEnd_4325217 : Nat := 740305085332569767432065

theorem tailTrace_4325217 : CollatzResearch.WordTrace tailWord_4325217 prefixEnd_4325217 740305085332569767432065 := by
  unfold tailWord_4325217
  simp only [CollatzResearch.WordTrace]
  refine ⟨157753623971484972098733905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105169082647656648065822603 157753623971484972098733905)
  ·
    refine ⟨118315217978613729074050429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157753623971484972098733905 118315217978613729074050429)
    ·
      refine ⟨44368206741980148402768911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118315217978613729074050429 44368206741980148402768911)
      ·
        refine ⟨66552310112970222604153367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44368206741980148402768911 66552310112970222604153367)
        ·
          refine ⟨99828465169455333906230051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66552310112970222604153367 99828465169455333906230051)
          ·
            refine ⟨149742697754183000859345077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99828465169455333906230051 149742697754183000859345077)
            ·
              refine ⟨14038377914454656330563601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149742697754183000859345077 14038377914454656330563601)
              ·
                refine ⟨10528783435840992247922701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14038377914454656330563601 10528783435840992247922701)
                ·
                  refine ⟨3948293788440372092971013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10528783435840992247922701 3948293788440372092971013)
                  ·
                    refine ⟨740305085332569767432065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948293788440372092971013 740305085332569767432065)
                    ·
                      rfl

theorem cell23_4325217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_4325217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325217 prefixEnd_4325217 := by exact prefixLift 4325217
  have htrace : WordTrace (prefixWord ++ tailWord_4325217) baseStart_4325217 baseEnd_4325217 := by
    simpa [prefixWord, tailWord_4325217, baseEnd_4325217] using wordTrace_append hprefix tailTrace_4325217
  have hstable : (prefixWord ++ tailWord_4325217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325217).length < 2 ^ (prefixWord ++ tailWord_4325217).sum := by decide
  have hdescent : baseEnd_4325217 < baseStart_4325217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325284 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_4325284 : Nat := 118140960795 + 4325284 * 2 ^ 59
def prefixEnd_4325284 : Nat := 4983230072969 + 3 ^ 40 * 4325284 * 2
def baseEnd_4325284 : Nat := 2220949659201560540158387

theorem tailTrace_4325284 : CollatzResearch.WordTrace tailWord_4325284 prefixEnd_4325284 2220949659201560540158387 := by
  unfold tailWord_4325284
  simp only [CollatzResearch.WordTrace]
  refine ⟨78878033831121121270711453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105170711774828161694281937 78878033831121121270711453)
  ·
    refine ⟨29579262686670420476516795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78878033831121121270711453 29579262686670420476516795)
    ·
      refine ⟨44368894030005630714775193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29579262686670420476516795 44368894030005630714775193)
      ·
        refine ⟨33276670522504223036081395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44368894030005630714775193 33276670522504223036081395)
        ·
          refine ⟨49915005783756334554122093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33276670522504223036081395 49915005783756334554122093)
          ·
            refine ⟨18718127168908625457795785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49915005783756334554122093 18718127168908625457795785)
            ·
              refine ⟨14038595376681469093346839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18718127168908625457795785 14038595376681469093346839)
              ·
                refine ⟨21057893065022203640020259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14038595376681469093346839 21057893065022203640020259)
                ·
                  refine ⟨31586839597533305460030389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21057893065022203640020259 31586839597533305460030389)
                  ·
                    refine ⟨2961266212268747386877849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31586839597533305460030389 2961266212268747386877849)
                    ·
                      refine ⟨2220949659201560540158387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961266212268747386877849 2220949659201560540158387)
                      ·
                        rfl

theorem cell23_4325284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_4325284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325284 prefixEnd_4325284 := by exact prefixLift 4325284
  have htrace : WordTrace (prefixWord ++ tailWord_4325284) baseStart_4325284 baseEnd_4325284 := by
    simpa [prefixWord, tailWord_4325284, baseEnd_4325284] using wordTrace_append hprefix tailTrace_4325284
  have hstable : (prefixWord ++ tailWord_4325284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325284).length < 2 ^ (prefixWord ++ tailWord_4325284).sum := by decide
  have hdescent : baseEnd_4325284 < baseStart_4325284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325301 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_4325301 : Nat := 118140960795 + 4325301 * 2 ^ 59
def prefixEnd_4325301 : Nat := 4983230072969 + 3 ^ 40 * 4325301 * 2
def baseEnd_4325301 : Nat := 2220958388372686973645809

theorem tailTrace_4325301 : CollatzResearch.WordTrace tailWord_4325301 prefixEnd_4325301 2220958388372686973645809 := by
  unfold tailWord_4325301
  simp only [CollatzResearch.WordTrace]
  refine ⟨157756687703180654444791757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105171125135453769629861171 157756687703180654444791757)
  ·
    refine ⟨59158757888692745416796909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157756687703180654444791757 59158757888692745416796909)
    ·
      refine ⟨22184534208259779531298841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59158757888692745416796909 22184534208259779531298841)
      ·
        refine ⟨16638400656194834648474131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22184534208259779531298841 16638400656194834648474131)
        ·
          refine ⟨24957600984292251972711197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16638400656194834648474131 24957600984292251972711197)
          ·
            refine ⟨9359100369109594489766699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24957600984292251972711197 9359100369109594489766699)
            ·
              refine ⟨14038650553664391734650049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9359100369109594489766699 14038650553664391734650049)
              ·
                refine ⟨10528987915248293800987537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14038650553664391734650049 10528987915248293800987537)
                ·
                  refine ⟨7896740936436220350740653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10528987915248293800987537 7896740936436220350740653)
                  ·
                    refine ⟨2961277851163582631527745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7896740936436220350740653 2961277851163582631527745)
                    ·
                      refine ⟨2220958388372686973645809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961277851163582631527745 2220958388372686973645809)
                      ·
                        rfl

theorem cell23_4325301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_4325301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325301 prefixEnd_4325301 := by exact prefixLift 4325301
  have htrace : WordTrace (prefixWord ++ tailWord_4325301) baseStart_4325301 baseEnd_4325301 := by
    simpa [prefixWord, tailWord_4325301, baseEnd_4325301] using wordTrace_append hprefix tailTrace_4325301
  have hstable : (prefixWord ++ tailWord_4325301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325301).length < 2 ^ (prefixWord ++ tailWord_4325301).sum := by decide
  have hdescent : baseEnd_4325301 < baseStart_4325301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325327 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_4325327 : Nat := 118140960795 + 4325327 * 2 ^ 59
def prefixEnd_4325327 : Nat := 4983230072969 + 3 ^ 40 * 4325327 * 2
def baseEnd_4325327 : Nat := 2220971738869703871920689

theorem tailTrace_4325327 : CollatzResearch.WordTrace tailWord_4325327 prefixEnd_4325327 2220971738869703871920689 := by
  unfold tailWord_4325327
  simp only [CollatzResearch.WordTrace]
  refine ⟨157757636001086460885238235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105171757334057640590158823 157757636001086460885238235)
  ·
    refine ⟨236636454001629691327857353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157757636001086460885238235 236636454001629691327857353)
    ·
      refine ⟨177477340501222268495893015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236636454001629691327857353 177477340501222268495893015)
      ·
        refine ⟨266216010751833402743839523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177477340501222268495893015 266216010751833402743839523)
        ·
          refine ⟨399324016127750104115759285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266216010751833402743839523 399324016127750104115759285)
          ·
            refine ⟨37436626511976572260852433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 399324016127750104115759285 37436626511976572260852433)
            ·
              refine ⟨28077469883982429195639325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37436626511976572260852433 28077469883982429195639325)
              ·
                refine ⟨10529051206493410948364747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28077469883982429195639325 10529051206493410948364747)
                ·
                  refine ⟨15793576809740116422547121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10529051206493410948364747 15793576809740116422547121)
                  ·
                    refine ⟨11845182607305087316910341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15793576809740116422547121 11845182607305087316910341)
                    ·
                      refine ⟨2220971738869703871920689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11845182607305087316910341 2220971738869703871920689)
                      ·
                        rfl

theorem cell23_4325327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_4325327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325327 prefixEnd_4325327 := by exact prefixLift 4325327
  have htrace : WordTrace (prefixWord ++ tailWord_4325327) baseStart_4325327 baseEnd_4325327 := by
    simpa [prefixWord, tailWord_4325327, baseEnd_4325327] using wordTrace_append hprefix tailTrace_4325327
  have hstable : (prefixWord ++ tailWord_4325327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325327).length < 2 ^ (prefixWord ++ tailWord_4325327).sum := by decide
  have hdescent : baseEnd_4325327 < baseStart_4325327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325348 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_4325348 : Nat := 118140960795 + 4325348 * 2 ^ 59
def prefixEnd_4325348 : Nat := 4983230072969 + 3 ^ 40 * 4325348 * 2
def baseEnd_4325348 : Nat := 2220982521963448289758093

theorem tailTrace_4325348 : CollatzResearch.WordTrace tailWord_4325348 prefixEnd_4325348 2220982521963448289758093 := by
  unfold tailWord_4325348
  simp only [CollatzResearch.WordTrace]
  refine ⟨78879200967005190735876349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105172267956006920981168465 78879200967005190735876349)
  ·
    refine ⟨29579700362626946525953631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78879200967005190735876349 29579700362626946525953631)
    ·
      refine ⟨44369550543940419788930447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29579700362626946525953631 44369550543940419788930447)
      ·
        refine ⟨66554325815910629683395671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44369550543940419788930447 66554325815910629683395671)
        ·
          refine ⟨99831488723865944525093507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66554325815910629683395671 99831488723865944525093507)
          ·
            refine ⟨149747233085798916787640261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99831488723865944525093507 149747233085798916787640261)
            ·
              refine ⟨28077606203587296897682549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149747233085798916787640261 28077606203587296897682549)
              ·
                refine ⟨2632275581586309084157739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28077606203587296897682549 2632275581586309084157739)
                ·
                  refine ⟨3948413372379463626236609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632275581586309084157739 3948413372379463626236609)
                  ·
                    refine ⟨2961310029284597719677457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948413372379463626236609 2961310029284597719677457)
                    ·
                      refine ⟨2220982521963448289758093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961310029284597719677457 2220982521963448289758093)
                      ·
                        rfl

theorem cell23_4325348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_4325348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325348 prefixEnd_4325348 := by exact prefixLift 4325348
  have htrace : WordTrace (prefixWord ++ tailWord_4325348) baseStart_4325348 baseEnd_4325348 := by
    simpa [prefixWord, tailWord_4325348, baseEnd_4325348] using wordTrace_append hprefix tailTrace_4325348
  have hstable : (prefixWord ++ tailWord_4325348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325348).length < 2 ^ (prefixWord ++ tailWord_4325348).sum := by decide
  have hdescent : baseEnd_4325348 < baseStart_4325348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325351 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4325351 : Nat := 118140960795 + 4325351 * 2 ^ 59
def prefixEnd_4325351 : Nat := 4983230072969 + 3 ^ 40 * 4325351 * 2
def baseEnd_4325351 : Nat := 2220984062405411778020579

theorem tailTrace_4325351 : CollatzResearch.WordTrace tailWord_4325351 prefixEnd_4325351 2220984062405411778020579 := by
  unfold tailWord_4325351
  simp only [CollatzResearch.WordTrace]
  refine ⟨157758511352999512984111907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105172340901999675322741271 157758511352999512984111907)
  ·
    refine ⟨236637767029499269476167861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157758511352999512984111907 236637767029499269476167861)
    ·
      refine ⟨22184790659015556513390737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 236637767029499269476167861 22184790659015556513390737)
      ·
        refine ⟨16638592994261667385043053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22184790659015556513390737 16638592994261667385043053)
        ·
          refine ⟨6239472372848125269391145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16638592994261667385043053 6239472372848125269391145)
          ·
            refine ⟨4679604279636093952043359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6239472372848125269391145 4679604279636093952043359)
            ·
              refine ⟨7019406419454140928065039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679604279636093952043359 7019406419454140928065039)
              ·
                refine ⟨10529109629181211392097559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7019406419454140928065039 10529109629181211392097559)
                ·
                  refine ⟨15793664443771817088146339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10529109629181211392097559 15793664443771817088146339)
                  ·
                    refine ⟨23690496665657725632219509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15793664443771817088146339 23690496665657725632219509)
                    ·
                      refine ⟨2220984062405411778020579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23690496665657725632219509 2220984062405411778020579)
                      ·
                        rfl

theorem cell23_4325351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4325351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325351 prefixEnd_4325351 := by exact prefixLift 4325351
  have htrace : WordTrace (prefixWord ++ tailWord_4325351) baseStart_4325351 baseEnd_4325351 := by
    simpa [prefixWord, tailWord_4325351, baseEnd_4325351] using wordTrace_append hprefix tailTrace_4325351
  have hstable : (prefixWord ++ tailWord_4325351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325351).length < 2 ^ (prefixWord ++ tailWord_4325351).sum := by decide
  have hdescent : baseEnd_4325351 < baseStart_4325351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325381 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_4325381 : Nat := 118140960795 + 4325381 * 2 ^ 59
def prefixEnd_4325381 : Nat := 4983230072969 + 3 ^ 40 * 4325381 * 2
def baseEnd_4325381 : Nat := 2220999466825046660645441

theorem tailTrace_4325381 : CollatzResearch.WordTrace tailWord_4325381 prefixEnd_4325381 2220999466825046660645441 := by
  unfold tailWord_4325381
  simp only [CollatzResearch.WordTrace]
  refine ⟨157759605542890828107703997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105173070361927218738469331 157759605542890828107703997)
  ·
    refine ⟨59159852078584060540388999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157759605542890828107703997 59159852078584060540388999)
    ·
      refine ⟨88739778117876090810583499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59159852078584060540388999 88739778117876090810583499)
      ·
        refine ⟨133109667176814136215875249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88739778117876090810583499 133109667176814136215875249)
        ·
          refine ⟨99832250382610602161906437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133109667176814136215875249 99832250382610602161906437)
          ·
            refine ⟨18718546946739487905357457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99832250382610602161906437 18718546946739487905357457)
            ·
              refine ⟨14038910210054615929018093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18718546946739487905357457 14038910210054615929018093)
              ·
                refine ⟨5264591328770480973381785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14038910210054615929018093 5264591328770480973381785)
                ·
                  refine ⟨3948443496577860730036339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5264591328770480973381785 3948443496577860730036339)
                  ·
                    refine ⟨5922665244866791095054509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3948443496577860730036339 5922665244866791095054509)
                    ·
                      refine ⟨2220999466825046660645441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5922665244866791095054509 2220999466825046660645441)
                      ·
                        rfl

theorem cell23_4325381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_4325381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325381 prefixEnd_4325381 := by exact prefixLift 4325381
  have htrace : WordTrace (prefixWord ++ tailWord_4325381) baseStart_4325381 baseEnd_4325381 := by
    simpa [prefixWord, tailWord_4325381, baseEnd_4325381] using wordTrace_append hprefix tailTrace_4325381
  have hstable : (prefixWord ++ tailWord_4325381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325381).length < 2 ^ (prefixWord ++ tailWord_4325381).sum := by decide
  have hdescent : baseEnd_4325381 < baseStart_4325381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325387 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4]
def baseStart_4325387 : Nat := 118140960795 + 4325387 * 2 ^ 59
def prefixEnd_4325387 : Nat := 4983230072969 + 3 ^ 40 * 4325387 * 2
def baseEnd_4325387 : Nat := 2221002547708973637170413

theorem tailTrace_4325387 : CollatzResearch.WordTrace tailWord_4325387 prefixEnd_4325387 2221002547708973637170413 := by
  unfold tailWord_4325387
  simp only [CollatzResearch.WordTrace]
  refine ⟨157759824380869091132422415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105173216253912727421614943 157759824380869091132422415)
  ·
    refine ⟨236639736571303636698633623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157759824380869091132422415 236639736571303636698633623)
    ·
      refine ⟨354959604856955455047950435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236639736571303636698633623 354959604856955455047950435)
      ·
        refine ⟨532439407285433182571925653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354959604856955455047950435 532439407285433182571925653)
        ·
          refine ⟨24958097216504680433059015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 532439407285433182571925653 24958097216504680433059015)
          ·
            refine ⟨37437145824757020649588523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24958097216504680433059015 37437145824757020649588523)
            ·
              refine ⟨56155718737135530974382785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37437145824757020649588523 56155718737135530974382785)
              ·
                refine ⟨42116789052851648230787089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56155718737135530974382785 42116789052851648230787089)
                ·
                  refine ⟨31587591789638736173090317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42116789052851648230787089 31587591789638736173090317)
                  ·
                    refine ⟨11845346921114526064908869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31587591789638736173090317 11845346921114526064908869)
                    ·
                      refine ⟨2221002547708973637170413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11845346921114526064908869 2221002547708973637170413)
                      ·
                        rfl

theorem cell23_4325387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_4325387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325387 prefixEnd_4325387 := by exact prefixLift 4325387
  have htrace : WordTrace (prefixWord ++ tailWord_4325387) baseStart_4325387 baseEnd_4325387 := by
    simpa [prefixWord, tailWord_4325387, baseEnd_4325387] using wordTrace_append hprefix tailTrace_4325387
  have hstable : (prefixWord ++ tailWord_4325387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325387).length < 2 ^ (prefixWord ++ tailWord_4325387).sum := by decide
  have hdescent : baseEnd_4325387 < baseStart_4325387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325407 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_4325407 : Nat := 118140960795 + 4325407 * 2 ^ 59
def prefixEnd_4325407 : Nat := 4983230072969 + 3 ^ 40 * 4325407 * 2
def baseEnd_4325407 : Nat := 2221012817322063558920321

theorem tailTrace_4325407 : CollatzResearch.WordTrace tailWord_4325407 prefixEnd_4325407 2221012817322063558920321 := by
  unfold tailWord_4325407
  simp only [CollatzResearch.WordTrace]
  refine ⟨157760553840796634548150475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105173702560531089698766983 157760553840796634548150475)
  ·
    refine ⟨236640830761194951822225713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157760553840796634548150475 236640830761194951822225713)
    ·
      refine ⟨177480623070896213866669285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236640830761194951822225713 177480623070896213866669285)
      ·
        refine ⟨33277616825793040100000491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177480623070896213866669285 33277616825793040100000491)
        ·
          refine ⟨49916425238689560150000737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33277616825793040100000491 49916425238689560150000737)
          ·
            refine ⟨37437318929017170112500553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49916425238689560150000737 37437318929017170112500553)
            ·
              refine ⟨28077989196762877584375415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37437318929017170112500553 28077989196762877584375415)
              ·
                refine ⟨42116983795144316376563123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28077989196762877584375415 42116983795144316376563123)
                ·
                  refine ⟨63175475692716474564844685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42116983795144316376563123 63175475692716474564844685)
                  ·
                    refine ⟨23690803384768677961816757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63175475692716474564844685 23690803384768677961816757)
                    ·
                      refine ⟨2221012817322063558920321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23690803384768677961816757 2221012817322063558920321)
                      ·
                        rfl

theorem cell23_4325407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_4325407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325407 prefixEnd_4325407 := by exact prefixLift 4325407
  have htrace : WordTrace (prefixWord ++ tailWord_4325407) baseStart_4325407 baseEnd_4325407 := by
    simpa [prefixWord, tailWord_4325407, baseEnd_4325407] using wordTrace_append hprefix tailTrace_4325407
  have hstable : (prefixWord ++ tailWord_4325407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325407).length < 2 ^ (prefixWord ++ tailWord_4325407).sum := by decide
  have hdescent : baseEnd_4325407 < baseStart_4325407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325427 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 7]
def baseStart_4325427 : Nat := 118140960795 + 4325427 * 2 ^ 59
def prefixEnd_4325427 : Nat := 4983230072969 + 3 ^ 40 * 4325427 * 2
def baseEnd_4325427 : Nat := 246780342992794831185581

theorem tailTrace_4325427 : CollatzResearch.WordTrace tailWord_4325427 prefixEnd_4325427 246780342992794831185581 := by
  unfold tailWord_4325427
  simp only [CollatzResearch.WordTrace]
  refine ⟨157761283300724177963878535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105174188867149451975919023 157761283300724177963878535)
  ·
    refine ⟨236641924951086266945817803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157761283300724177963878535 236641924951086266945817803)
    ·
      refine ⟨354962887426629400418726705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236641924951086266945817803 354962887426629400418726705)
      ·
        refine ⟨266222165569972050314045029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354962887426629400418726705 266222165569972050314045029)
        ·
          refine ⟨49916656044369759433883443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266222165569972050314045029 49916656044369759433883443)
          ·
            refine ⟨74874984066554639150825165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49916656044369759433883443 74874984066554639150825165)
            ·
              refine ⟨28078119024957989681559437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74874984066554639150825165 28078119024957989681559437)
              ·
                refine ⟨10529294634359246130584789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28078119024957989681559437 10529294634359246130584789)
                ·
                  refine ⟨246780342992794831185581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10529294634359246130584789 246780342992794831185581)
                  ·
                    rfl

theorem cell23_4325427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 7].length) (baseStart_4325427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325427 prefixEnd_4325427 := by exact prefixLift 4325427
  have htrace : WordTrace (prefixWord ++ tailWord_4325427) baseStart_4325427 baseEnd_4325427 := by
    simpa [prefixWord, tailWord_4325427, baseEnd_4325427] using wordTrace_append hprefix tailTrace_4325427
  have hstable : (prefixWord ++ tailWord_4325427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325427).length < 2 ^ (prefixWord ++ tailWord_4325427).sum := by decide
  have hdescent : baseEnd_4325427 < baseStart_4325427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325461 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 5]
def baseStart_4325461 : Nat := 118140960795 + 4325461 * 2 ^ 59
def prefixEnd_4325461 : Nat := 4983230072969 + 3 ^ 40 * 4325461 * 2
def baseEnd_4325461 : Nat := 246782282808600705293897

theorem tailTrace_4325461 : CollatzResearch.WordTrace tailWord_4325461 prefixEnd_4325461 246782282808600705293897 := by
  unfold tailWord_4325461
  simp only [CollatzResearch.WordTrace]
  refine ⟨157762523382601001770616237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105175015588400667847077491 157762523382601001770616237)
  ·
    refine ⟨59160946268475375663981089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157762523382601001770616237 59160946268475375663981089)
    ·
      refine ⟨44370709701356531747985817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59160946268475375663981089 44370709701356531747985817)
      ·
        refine ⟨33278032276017398810989363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44370709701356531747985817 33278032276017398810989363)
        ·
          refine ⟨49917048414026098216484045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33278032276017398810989363 49917048414026098216484045)
          ·
            refine ⟨18718893155259786831181517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49917048414026098216484045 18718893155259786831181517)
            ·
              refine ⟨7019584933222420061693069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18718893155259786831181517 7019584933222420061693069)
              ·
                refine ⟨2632344349958407523134901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7019584933222420061693069 2632344349958407523134901)
                ·
                  refine ⟨246782282808600705293897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632344349958407523134901 246782282808600705293897)
                  ·
                    rfl

theorem cell23_4325461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_4325461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325461 prefixEnd_4325461 := by exact prefixLift 4325461
  have htrace : WordTrace (prefixWord ++ tailWord_4325461) baseStart_4325461 baseEnd_4325461 := by
    simpa [prefixWord, tailWord_4325461, baseEnd_4325461] using wordTrace_append hprefix tailTrace_4325461
  have hstable : (prefixWord ++ tailWord_4325461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325461).length < 2 ^ (prefixWord ++ tailWord_4325461).sum := by decide
  have hdescent : baseEnd_4325461 < baseStart_4325461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325484 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_4325484 : Nat := 118140960795 + 4325484 * 2 ^ 59
def prefixEnd_4325484 : Nat := 4983230072969 + 3 ^ 40 * 4325484 * 2
def baseEnd_4325484 : Nat := 2221052355332459757657467

theorem tailTrace_4325484 : CollatzResearch.WordTrace tailWord_4325484 prefixEnd_4325484 2221052355332459757657467 := by
  unfold tailWord_4325484
  simp only [CollatzResearch.WordTrace]
  refine ⟨78881681130758838349351753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105175574841011784465802337 78881681130758838349351753)
  ·
    refine ⟨59161260848069128762013815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78881681130758838349351753 59161260848069128762013815)
    ·
      refine ⟨88741891272103693143020723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59161260848069128762013815 88741891272103693143020723)
      ·
        refine ⟨133112836908155539714531085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88741891272103693143020723 133112836908155539714531085)
        ·
          refine ⟨49917313840558327392949157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133112836908155539714531085 49917313840558327392949157)
          ·
            refine ⟨9359496345104686386177967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49917313840558327392949157 9359496345104686386177967)
            ·
              refine ⟨14039244517657029579266951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9359496345104686386177967 14039244517657029579266951)
              ·
                refine ⟨21058866776485544368900427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14039244517657029579266951 21058866776485544368900427)
                ·
                  refine ⟨31588300164728316553350641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21058866776485544368900427 31588300164728316553350641)
                  ·
                    refine ⟨23691225123546237415012981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31588300164728316553350641 23691225123546237415012981)
                    ·
                      refine ⟨2221052355332459757657467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23691225123546237415012981 2221052355332459757657467)
                      ·
                        rfl

theorem cell23_4325484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_4325484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325484 prefixEnd_4325484 := by exact prefixLift 4325484
  have htrace : WordTrace (prefixWord ++ tailWord_4325484) baseStart_4325484 baseEnd_4325484 := by
    simpa [prefixWord, tailWord_4325484, baseEnd_4325484] using wordTrace_append hprefix tailTrace_4325484
  have hstable : (prefixWord ++ tailWord_4325484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325484).length < 2 ^ (prefixWord ++ tailWord_4325484).sum := by decide
  have hdescent : baseEnd_4325484 < baseStart_4325484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325504 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 5, 4]
def baseStart_4325504 : Nat := 118140960795 + 4325504 * 2 ^ 59
def prefixEnd_4325504 : Nat := 4983230072969 + 3 ^ 40 * 4325504 * 2
def baseEnd_4325504 : Nat := 740354208315183226469125

theorem tailTrace_4325504 : CollatzResearch.WordTrace tailWord_4325504 prefixEnd_4325504 740354208315183226469125 := by
  unfold tailWord_4325504
  simp only [CollatzResearch.WordTrace]
  refine ⟨78882045860722610057215783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105176061147630146742954377 78882045860722610057215783)
  ·
    refine ⟨118323068791083915085823675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78882045860722610057215783 118323068791083915085823675)
    ·
      refine ⟨177484603186625872628735513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118323068791083915085823675 177484603186625872628735513)
      ·
        refine ⟨133113452389969404471551635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177484603186625872628735513 133113452389969404471551635)
        ·
          refine ⟨199670178584954106707327453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133113452389969404471551635 199670178584954106707327453)
          ·
            refine ⟨74876316969357790015247795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199670178584954106707327453 74876316969357790015247795)
            ·
              refine ⟨112314475454036685022871693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74876316969357790015247795 112314475454036685022871693)
              ·
                refine ⟨42117928295263756883576885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112314475454036685022871693 42117928295263756883576885)
                ·
                  refine ⟨3948555777680977207835333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42117928295263756883576885 3948555777680977207835333)
                  ·
                    refine ⟨740354208315183226469125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948555777680977207835333 740354208315183226469125)
                    ·
                      rfl

theorem cell23_4325504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_4325504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325504 prefixEnd_4325504 := by exact prefixLift 4325504
  have htrace : WordTrace (prefixWord ++ tailWord_4325504) baseStart_4325504 baseEnd_4325504 := by
    simpa [prefixWord, tailWord_4325504, baseEnd_4325504] using wordTrace_append hprefix tailTrace_4325504
  have hstable : (prefixWord ++ tailWord_4325504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325504).length < 2 ^ (prefixWord ++ tailWord_4325504).sum := by decide
  have hdescent : baseEnd_4325504 < baseStart_4325504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325594 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_4325594 : Nat := 118140960795 + 4325594 * 2 ^ 59
def prefixEnd_4325594 : Nat := 4983230072969 + 3 ^ 40 * 4325594 * 2
def baseEnd_4325594 : Nat := 740369612734818109093987

theorem tailTrace_4325594 : CollatzResearch.WordTrace tailWord_4325594 prefixEnd_4325594 740369612734818109093987 := by
  unfold tailWord_4325594
  simp only [CollatzResearch.WordTrace]
  refine ⟨39441843572779791371301959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105178249527412776990138557 39441843572779791371301959)
  ·
    refine ⟨59162765359169687056952939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39441843572779791371301959 59162765359169687056952939)
    ·
      refine ⟨88744148038754530585429409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59162765359169687056952939 88744148038754530585429409)
      ·
        refine ⟨66558111029065897939072057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88744148038754530585429409 66558111029065897939072057)
        ·
          refine ⟨49918583271799423454304043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66558111029065897939072057 49918583271799423454304043)
          ·
            refine ⟨74877874907699135181456065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49918583271799423454304043 74877874907699135181456065)
            ·
              refine ⟨56158406180774351386092049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74877874907699135181456065 56158406180774351386092049)
              ·
                refine ⟨42118804635580763539569037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56158406180774351386092049 42118804635580763539569037)
                ·
                  refine ⟨15794551738342786327338389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42118804635580763539569037 15794551738342786327338389)
                  ·
                    refine ⟨740369612734818109093987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15794551738342786327338389 740369612734818109093987)
                    ·
                      rfl

theorem cell23_4325594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_4325594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325594 prefixEnd_4325594 := by exact prefixLift 4325594
  have htrace : WordTrace (prefixWord ++ tailWord_4325594) baseStart_4325594 baseEnd_4325594 := by
    simpa [prefixWord, tailWord_4325594, baseEnd_4325594] using wordTrace_append hprefix tailTrace_4325594
  have hstable : (prefixWord ++ tailWord_4325594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325594).length < 2 ^ (prefixWord ++ tailWord_4325594).sum := by decide
  have hdescent : baseEnd_4325594 < baseStart_4325594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325618 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4325618 : Nat := 118140960795 + 4325618 * 2 ^ 59
def prefixEnd_4325618 : Nat := 4983230072969 + 3 ^ 40 * 4325618 * 2
def baseEnd_4325618 : Nat := 2221121161740162233381851

theorem tailTrace_4325618 : CollatzResearch.WordTrace tailWord_4325618 prefixEnd_4325618 2221121161740162233381851 := by
  unfold tailWord_4325618
  simp only [CollatzResearch.WordTrace]
  refine ⟨39442062410758054396020377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105178833095354811722721005 39442062410758054396020377)
  ·
    refine ⟨29581546808068540797015283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39442062410758054396020377 29581546808068540797015283)
    ·
      refine ⟨44372320212102811195522925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29581546808068540797015283 44372320212102811195522925)
      ·
        refine ⟨16639620079538554198321097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44372320212102811195522925 16639620079538554198321097)
        ·
          refine ⟨12479715059653915648740823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16639620079538554198321097 12479715059653915648740823)
          ·
            refine ⟨18719572589480873473111235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12479715059653915648740823 18719572589480873473111235)
            ·
              refine ⟨28079358884221310209666853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18719572589480873473111235 28079358884221310209666853)
              ·
                refine ⟨5264879790791495664312535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28079358884221310209666853 5264879790791495664312535)
                ·
                  refine ⟨7897319686187243496468803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5264879790791495664312535 7897319686187243496468803)
                  ·
                    refine ⟨11845979529280865244703205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7897319686187243496468803 11845979529280865244703205)
                    ·
                      refine ⟨2221121161740162233381851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11845979529280865244703205 2221121161740162233381851)
                      ·
                        rfl

theorem cell23_4325618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4325618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325618 prefixEnd_4325618 := by exact prefixLift 4325618
  have htrace : WordTrace (prefixWord ++ tailWord_4325618) baseStart_4325618 baseEnd_4325618 := by
    simpa [prefixWord, tailWord_4325618, baseEnd_4325618] using wordTrace_append hprefix tailTrace_4325618
  have hstable : (prefixWord ++ tailWord_4325618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325618).length < 2 ^ (prefixWord ++ tailWord_4325618).sum := by decide
  have hdescent : baseEnd_4325618 < baseStart_4325618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325662 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4325662 : Nat := 118140960795 + 4325662 * 2 ^ 59
def prefixEnd_4325662 : Nat := 4983230072969 + 3 ^ 40 * 4325662 * 2
def baseEnd_4325662 : Nat := 740381251629653353743883

theorem tailTrace_4325662 : CollatzResearch.WordTrace tailWord_4325662 prefixEnd_4325662 740381251629653353743883 := by
  unfold tailWord_4325662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19721231806859101637335405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105179902969915208732455493 19721231806859101637335405)
  ·
    refine ⟨7395461927572163114000777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19721231806859101637335405 7395461927572163114000777)
    ·
      refine ⟨5546596445679122335500583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7395461927572163114000777 5546596445679122335500583)
      ·
        refine ⟨8319894668518683503250875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5546596445679122335500583 8319894668518683503250875)
        ·
          refine ⟨12479842002778025254876313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8319894668518683503250875 12479842002778025254876313)
          ·
            refine ⟨9359881502083518941157235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12479842002778025254876313 9359881502083518941157235)
            ·
              refine ⟨14039822253125278411735853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9359881502083518941157235 14039822253125278411735853)
              ·
                refine ⟨5264933344921979404400945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14039822253125278411735853 5264933344921979404400945)
                ·
                  refine ⟨3948700008691484553300709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5264933344921979404400945 3948700008691484553300709)
                  ·
                    refine ⟨740381251629653353743883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948700008691484553300709 740381251629653353743883)
                    ·
                      rfl

theorem cell23_4325662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4325662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325662 prefixEnd_4325662 := by exact prefixLift 4325662
  have htrace : WordTrace (prefixWord ++ tailWord_4325662) baseStart_4325662 baseEnd_4325662 := by
    simpa [prefixWord, tailWord_4325662, baseEnd_4325662] using wordTrace_append hprefix tailTrace_4325662
  have hstable : (prefixWord ++ tailWord_4325662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325662).length < 2 ^ (prefixWord ++ tailWord_4325662).sum := by decide
  have hdescent : baseEnd_4325662 < baseStart_4325662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325672 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_4325672 : Nat := 118140960795 + 4325672 * 2 ^ 59
def prefixEnd_4325672 : Nat := 4983230072969 + 3 ^ 40 * 4325672 * 2
def baseEnd_4325672 : Nat := 2221148889695505022106603

theorem tailTrace_4325672 : CollatzResearch.WordTrace tailWord_4325672 prefixEnd_4325672 2221148889695505022106603 := by
  unfold tailWord_4325672
  simp only [CollatzResearch.WordTrace]
  refine ⟨78885109592418292403273635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105180146123224389871031513 78885109592418292403273635)
  ·
    refine ⟨118327664388627438604910453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78885109592418292403273635 118327664388627438604910453)
    ·
      refine ⟨11093218536433822369210355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118327664388627438604910453 11093218536433822369210355)
      ·
        refine ⟨16639827804650733553815533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11093218536433822369210355 16639827804650733553815533)
        ·
          refine ⟨6239935426744025082680825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16639827804650733553815533 6239935426744025082680825)
          ·
            refine ⟨4679951570058018812010619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6239935426744025082680825 4679951570058018812010619)
            ·
              refine ⟨7019927355087028218015929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679951570058018812010619 7019927355087028218015929)
              ·
                refine ⟨5264945516315271163511947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7019927355087028218015929 5264945516315271163511947)
                ·
                  refine ⟨7897418274472906745267921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5264945516315271163511947 7897418274472906745267921)
                  ·
                    refine ⟨5923063705854680058950941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7897418274472906745267921 5923063705854680058950941)
                    ·
                      refine ⟨2221148889695505022106603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5923063705854680058950941 2221148889695505022106603)
                      ·
                        rfl

theorem cell23_4325672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_4325672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325672 prefixEnd_4325672 := by exact prefixLift 4325672
  have htrace : WordTrace (prefixWord ++ tailWord_4325672) baseStart_4325672 baseEnd_4325672 := by
    simpa [prefixWord, tailWord_4325672, baseEnd_4325672] using wordTrace_append hprefix tailTrace_4325672
  have hstable : (prefixWord ++ tailWord_4325672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325672).length < 2 ^ (prefixWord ++ tailWord_4325672).sum := by decide
  have hdescent : baseEnd_4325672 < baseStart_4325672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325708 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4325708 : Nat := 118140960795 + 4325708 * 2 ^ 59
def prefixEnd_4325708 : Nat := 4983230072969 + 3 ^ 40 * 4325708 * 2
def baseEnd_4325708 : Nat := 2221167374999066881256437

theorem tailTrace_4325708 : CollatzResearch.WordTrace tailWord_4325708 prefixEnd_4325708 2221167374999066881256437 := by
  unfold tailWord_4325708
  simp only [CollatzResearch.WordTrace]
  refine ⟨78885766106353081477428889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105181021475137441969905185 78885766106353081477428889)
  ·
    refine ⟨59164324579764811108071667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78885766106353081477428889 59164324579764811108071667)
    ·
      refine ⟨88746486869647216662107501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59164324579764811108071667 88746486869647216662107501)
      ·
        refine ⟨33279932576117706248290313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88746486869647216662107501 33279932576117706248290313)
        ·
          refine ⟨24959949432088279686217735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33279932576117706248290313 24959949432088279686217735)
          ·
            refine ⟨37439924148132419529326603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24959949432088279686217735 37439924148132419529326603)
            ·
              refine ⟨56159886222198629293989905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37439924148132419529326603 56159886222198629293989905)
              ·
                refine ⟨42119914666648971970492429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56159886222198629293989905 42119914666648971970492429)
                ·
                  refine ⟨15794967999993364488934661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42119914666648971970492429 15794967999993364488934661)
                  ·
                    refine ⟨2961556499998755841675249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15794967999993364488934661 2961556499998755841675249)
                    ·
                      refine ⟨2221167374999066881256437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961556499998755841675249 2221167374999066881256437)
                      ·
                        rfl

theorem cell23_4325708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4325708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325708 prefixEnd_4325708 := by exact prefixLift 4325708
  have htrace : WordTrace (prefixWord ++ tailWord_4325708) baseStart_4325708 baseEnd_4325708 := by
    simpa [prefixWord, tailWord_4325708, baseEnd_4325708] using wordTrace_append hprefix tailTrace_4325708
  have hstable : (prefixWord ++ tailWord_4325708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325708).length < 2 ^ (prefixWord ++ tailWord_4325708).sum := by decide
  have hdescent : baseEnd_4325708 < baseStart_4325708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325731 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 7]
def baseStart_4325731 : Nat := 118140960795 + 4325731 * 2 ^ 59
def prefixEnd_4325731 : Nat := 4983230072969 + 3 ^ 40 * 4325731 * 2
def baseEnd_4325731 : Nat := 246797687228235587918759

theorem tailTrace_4325731 : CollatzResearch.WordTrace tailWord_4325731 prefixEnd_4325731 246797687228235587918759 := by
  unfold tailWord_4325731
  simp only [CollatzResearch.WordTrace]
  refine ⟨157772371091622837882945047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105181580727748558588630031 157772371091622837882945047)
  ·
    refine ⟨236658556637434256824417571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157772371091622837882945047 236658556637434256824417571)
    ·
      refine ⟨354987834956151385236626357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236658556637434256824417571 354987834956151385236626357)
      ·
        refine ⟨33280109527139192365933721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 354987834956151385236626357 33280109527139192365933721)
        ·
          refine ⟨24960082145354394274450291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33280109527139192365933721 24960082145354394274450291)
          ·
            refine ⟨37440123218031591411675437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24960082145354394274450291 37440123218031591411675437)
            ·
              refine ⟨14040046206761846779378289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37440123218031591411675437 14040046206761846779378289)
              ·
                refine ⟨10530034655071385084533717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14040046206761846779378289 10530034655071385084533717)
                ·
                  refine ⟨246797687228235587918759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10530034655071385084533717 246797687228235587918759)
                  ·
                    rfl

theorem cell23_4325731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 7].length) (baseStart_4325731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325731 prefixEnd_4325731 := by exact prefixLift 4325731
  have htrace : WordTrace (prefixWord ++ tailWord_4325731) baseStart_4325731 baseEnd_4325731 := by
    simpa [prefixWord, tailWord_4325731, baseEnd_4325731] using wordTrace_append hprefix tailTrace_4325731
  have hstable : (prefixWord ++ tailWord_4325731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325731).length < 2 ^ (prefixWord ++ tailWord_4325731).sum := by decide
  have hdescent : baseEnd_4325731 < baseStart_4325731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325791 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 8]
def baseStart_4325791 : Nat := 118140960795 + 4325791 * 2 ^ 59
def prefixEnd_4325791 : Nat := 4983230072969 + 3 ^ 40 * 4325791 * 2
def baseEnd_4325791 : Nat := 740403331297796685506185

theorem tailTrace_4325791 : CollatzResearch.WordTrace tailWord_4325791 prefixEnd_4325791 740403331297796685506185 := by
  unfold tailWord_4325791
  simp only [CollatzResearch.WordTrace]
  refine ⟨157774559471405468130129227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105183039647603645420086151 157774559471405468130129227)
  ·
    refine ⟨236661839207108202195193841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157774559471405468130129227 236661839207108202195193841)
    ·
      refine ⟨177496379405331151646395381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236661839207108202195193841 177496379405331151646395381)
      ·
        refine ⟨16640285569249795466849567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177496379405331151646395381 16640285569249795466849567)
        ·
          refine ⟨24960428353874693200274351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16640285569249795466849567 24960428353874693200274351)
          ·
            refine ⟨37440642530812039800411527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24960428353874693200274351 37440642530812039800411527)
            ·
              refine ⟨56160963796218059700617291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37440642530812039800411527 56160963796218059700617291)
              ·
                refine ⟨84241445694327089550925937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56160963796218059700617291 84241445694327089550925937)
                ·
                  refine ⟨63181084270745317163194453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84241445694327089550925937 63181084270745317163194453)
                  ·
                    refine ⟨740403331297796685506185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63181084270745317163194453 740403331297796685506185)
                    ·
                      rfl

theorem cell23_4325791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_4325791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325791 prefixEnd_4325791 := by exact prefixLift 4325791
  have htrace : WordTrace (prefixWord ++ tailWord_4325791) baseStart_4325791 baseEnd_4325791 := by
    simpa [prefixWord, tailWord_4325791, baseEnd_4325791] using wordTrace_append hprefix tailTrace_4325791
  have hstable : (prefixWord ++ tailWord_4325791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325791).length < 2 ^ (prefixWord ++ tailWord_4325791).sum := by decide
  have hdescent : baseEnd_4325791 < baseStart_4325791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325841 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_4325841 : Nat := 118140960795 + 4325841 * 2 ^ 59
def prefixEnd_4325841 : Nat := 4983230072969 + 3 ^ 40 * 4325841 * 2
def baseEnd_4325841 : Nat := 2221235667926114860893325

theorem tailTrace_4325841 : CollatzResearch.WordTrace tailWord_4325841 prefixEnd_4325841 2221235667926114860893325 := by
  unfold tailWord_4325841
  simp only [CollatzResearch.WordTrace]
  refine ⟨157776383121224326669449377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105184255414149551112966251 157776383121224326669449377)
  ·
    refine ⟨118332287340918245002087033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157776383121224326669449377 118332287340918245002087033)
    ·
      refine ⟨88749215505688683751565275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118332287340918245002087033 88749215505688683751565275)
      ·
        refine ⟨133123823258533025627347913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88749215505688683751565275 133123823258533025627347913)
        ·
          refine ⟨99842867443899769220510935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133123823258533025627347913 99842867443899769220510935)
          ·
            refine ⟨149764301165849653830766403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99842867443899769220510935 149764301165849653830766403)
            ·
              refine ⟨224646451748774480746149605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149764301165849653830766403 224646451748774480746149605)
              ·
                refine ⟨42121209702895215139903051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224646451748774480746149605 42121209702895215139903051)
                ·
                  refine ⟨63181814554342822709854577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42121209702895215139903051 63181814554342822709854577)
                  ·
                    refine ⟨47386360915757117032390933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63181814554342822709854577 47386360915757117032390933)
                    ·
                      refine ⟨2221235667926114860893325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47386360915757117032390933 2221235667926114860893325)
                      ·
                        rfl

theorem cell23_4325841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_4325841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325841 prefixEnd_4325841 := by exact prefixLift 4325841
  have htrace : WordTrace (prefixWord ++ tailWord_4325841) baseStart_4325841 baseEnd_4325841 := by
    simpa [prefixWord, tailWord_4325841, baseEnd_4325841] using wordTrace_append hprefix tailTrace_4325841
  have hstable : (prefixWord ++ tailWord_4325841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325841).length < 2 ^ (prefixWord ++ tailWord_4325841).sum := by decide
  have hdescent : baseEnd_4325841 < baseStart_4325841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325875 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 2, 3, 2]
def baseStart_4325875 : Nat := 118140960795 + 4325875 * 2 ^ 59
def prefixEnd_4325875 : Nat := 4983230072969 + 3 ^ 40 * 4325875 * 2
def baseEnd_4325875 : Nat := 2221253126268367727868169

theorem tailTrace_4325875 : CollatzResearch.WordTrace tailWord_4325875 prefixEnd_4325875 2221253126268367727868169 := by
  unfold tailWord_4325875
  simp only [CollatzResearch.WordTrace]
  refine ⟨157777623203101150476187079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105185082135400766984124719 157777623203101150476187079)
  ·
    refine ⟨236666434804651725714280619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157777623203101150476187079 236666434804651725714280619)
    ·
      refine ⟨354999652206977588571420929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236666434804651725714280619 354999652206977588571420929)
      ·
        refine ⟨266249739155233191428565697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354999652206977588571420929 266249739155233191428565697)
        ·
          refine ⟨199687304366424893571424273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266249739155233191428565697 199687304366424893571424273)
          ·
            refine ⟨149765478274818670178568205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199687304366424893571424273 149765478274818670178568205)
            ·
              refine ⟨56162054353057001316963077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149765478274818670178568205 56162054353057001316963077)
              ·
                refine ⟨10530385191198187746930577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56162054353057001316963077 10530385191198187746930577)
                ·
                  refine ⟨7897788893398640810197933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10530385191198187746930577 7897788893398640810197933)
                  ·
                    refine ⟨2961670835024490303824225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7897788893398640810197933 2961670835024490303824225)
                    ·
                      refine ⟨2221253126268367727868169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961670835024490303824225 2221253126268367727868169)
                      ·
                        rfl

theorem cell23_4325875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 3, 2].length) (baseStart_4325875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325875 prefixEnd_4325875 := by exact prefixLift 4325875
  have htrace : WordTrace (prefixWord ++ tailWord_4325875) baseStart_4325875 baseEnd_4325875 := by
    simpa [prefixWord, tailWord_4325875, baseEnd_4325875] using wordTrace_append hprefix tailTrace_4325875
  have hstable : (prefixWord ++ tailWord_4325875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325875).length < 2 ^ (prefixWord ++ tailWord_4325875).sum := by decide
  have hdescent : baseEnd_4325875 < baseStart_4325875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325922 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_4325922 : Nat := 118140960795 + 4325922 * 2 ^ 59
def prefixEnd_4325922 : Nat := 4983230072969 + 3 ^ 40 * 4325922 * 2
def baseEnd_4325922 : Nat := 2221277259859129043980453

theorem tailTrace_4325922 : CollatzResearch.WordTrace tailWord_4325922 prefixEnd_4325922 2221277259859129043980453 := by
  unfold tailWord_4325922
  simp only [CollatzResearch.WordTrace]
  refine ⟨39444834358482719375787005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105186224955953918335432013 39444834358482719375787005)
  ·
    refine ⟨14791812884431019765920127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39444834358482719375787005 14791812884431019765920127)
    ·
      refine ⟨22187719326646529648880191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14791812884431019765920127 22187719326646529648880191)
      ·
        refine ⟨33281578989969794473320287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22187719326646529648880191 33281578989969794473320287)
        ·
          refine ⟨49922368484954691709980431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33281578989969794473320287 49922368484954691709980431)
          ·
            refine ⟨74883552727432037564970647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49922368484954691709980431 74883552727432037564970647)
            ·
              refine ⟨112325329091148056347455971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74883552727432037564970647 112325329091148056347455971)
              ·
                refine ⟨168487993636722084521183957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112325329091148056347455971 168487993636722084521183957)
                ·
                  refine ⟨3948937350860673855965249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 168487993636722084521183957 3948937350860673855965249)
                  ·
                    refine ⟨2961703013145505391973937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948937350860673855965249 2961703013145505391973937)
                    ·
                      refine ⟨2221277259859129043980453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961703013145505391973937 2221277259859129043980453)
                      ·
                        rfl

theorem cell23_4325922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_4325922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325922 prefixEnd_4325922 := by exact prefixLift 4325922
  have htrace : WordTrace (prefixWord ++ tailWord_4325922) baseStart_4325922 baseEnd_4325922 := by
    simpa [prefixWord, tailWord_4325922, baseEnd_4325922] using wordTrace_append hprefix tailTrace_4325922
  have hstable : (prefixWord ++ tailWord_4325922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325922).length < 2 ^ (prefixWord ++ tailWord_4325922).sum := by decide
  have hdescent : baseEnd_4325922 < baseStart_4325922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325933 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4325933 : Nat := 118140960795 + 4325933 * 2 ^ 59
def prefixEnd_4325933 : Nat := 4983230072969 + 3 ^ 40 * 4325933 * 2
def baseEnd_4325933 : Nat := 2221282908146328500942903

theorem tailTrace_4325933 : CollatzResearch.WordTrace tailWord_4325933 prefixEnd_4325933 2221282908146328500942903 := by
  unfold tailWord_4325933
  simp only [CollatzResearch.WordTrace]
  refine ⟨157779738636891026381798453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105186492424594017587865635 157779738636891026381798453)
  ·
    refine ⟨14791850497208533723293605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157779738636891026381798453 14791850497208533723293605)
    ·
      refine ⟨2773471968226600073117551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14791850497208533723293605 2773471968226600073117551)
      ·
        refine ⟨4160207952339900109676327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773471968226600073117551 4160207952339900109676327)
        ·
          refine ⟨6240311928509850164514491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4160207952339900109676327 6240311928509850164514491)
          ·
            refine ⟨9360467892764775246771737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6240311928509850164514491 9360467892764775246771737)
            ·
              refine ⟨7020350919573581435078803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9360467892764775246771737 7020350919573581435078803)
              ·
                refine ⟨10530526379360372152618205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7020350919573581435078803 10530526379360372152618205)
                ·
                  refine ⟨3948947392260139557231827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10530526379360372152618205 3948947392260139557231827)
                  ·
                    refine ⟨5923421088390209335847741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3948947392260139557231827 5923421088390209335847741)
                    ·
                      refine ⟨2221282908146328500942903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5923421088390209335847741 2221282908146328500942903)
                      ·
                        rfl

theorem cell23_4325933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4325933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325933 prefixEnd_4325933 := by exact prefixLift 4325933
  have htrace : WordTrace (prefixWord ++ tailWord_4325933) baseStart_4325933 baseEnd_4325933 := by
    simpa [prefixWord, tailWord_4325933, baseEnd_4325933] using wordTrace_append hprefix tailTrace_4325933
  have hstable : (prefixWord ++ tailWord_4325933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325933).length < 2 ^ (prefixWord ++ tailWord_4325933).sum := by decide
  have hdescent : baseEnd_4325933 < baseStart_4325933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325939 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 1, 2, 2]
def baseStart_4325939 : Nat := 118140960795 + 4325939 * 2 ^ 59
def prefixEnd_4325939 : Nat := 4983230072969 + 3 ^ 40 * 4325939 * 2
def baseEnd_4325939 : Nat := 2221285989030255477467875

theorem tailTrace_4325939 : CollatzResearch.WordTrace tailWord_4325939 prefixEnd_4325939 2221285989030255477467875 := by
  unfold tailWord_4325939
  simp only [CollatzResearch.WordTrace]
  refine ⟨157779957474869289406516871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105186638316579526271011247 157779957474869289406516871)
  ·
    refine ⟨236669936212303934109775307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157779957474869289406516871 236669936212303934109775307)
    ·
      refine ⟨355004904318455901164662961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236669936212303934109775307 355004904318455901164662961)
      ·
        refine ⟨266253678238841925873497221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355004904318455901164662961 266253678238841925873497221)
        ·
          refine ⟨49922564669782861101280729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266253678238841925873497221 49922564669782861101280729)
          ·
            refine ⟨37441923502337145825960547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49922564669782861101280729 37441923502337145825960547)
            ·
              refine ⟨56162885253505718738940821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37441923502337145825960547 56162885253505718738940821)
              ·
                refine ⟨2632635246258080565887851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56162885253505718738940821 2632635246258080565887851)
                ·
                  refine ⟨3948952869387120848831777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632635246258080565887851 3948952869387120848831777)
                  ·
                    refine ⟨2961714652040340636623833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3948952869387120848831777 2961714652040340636623833)
                    ·
                      refine ⟨2221285989030255477467875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961714652040340636623833 2221285989030255477467875)
                      ·
                        rfl

theorem cell23_4325939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 1, 2, 2].length) (baseStart_4325939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325939 prefixEnd_4325939 := by exact prefixLift 4325939
  have htrace : WordTrace (prefixWord ++ tailWord_4325939) baseStart_4325939 baseEnd_4325939 := by
    simpa [prefixWord, tailWord_4325939, baseEnd_4325939] using wordTrace_append hprefix tailTrace_4325939
  have hstable : (prefixWord ++ tailWord_4325939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325939).length < 2 ^ (prefixWord ++ tailWord_4325939).sum := by decide
  have hdescent : baseEnd_4325939 < baseStart_4325939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325942 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4325942 : Nat := 118140960795 + 4325942 * 2 ^ 59
def prefixEnd_4325942 : Nat := 4983230072969 + 3 ^ 40 * 4325942 * 2
def baseEnd_4325942 : Nat := 2221287529472218965730361

theorem tailTrace_4325942 : CollatzResearch.WordTrace tailWord_4325942 prefixEnd_4325942 2221287529472218965730361 := by
  unfold tailWord_4325942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861254180866151307429755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105186711262572280612584053 9861254180866151307429755)
  ·
    refine ⟨14791881271299226961144633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9861254180866151307429755 14791881271299226961144633)
    ·
      refine ⟨11093910953474420220858475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14791881271299226961144633 11093910953474420220858475)
      ·
        refine ⟨16640866430211630331287713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11093910953474420220858475 16640866430211630331287713)
        ·
          refine ⟨12480649822658722748465785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16640866430211630331287713 12480649822658722748465785)
          ·
            refine ⟨9360487366994042061349339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12480649822658722748465785 9360487366994042061349339)
            ·
              refine ⟨14040731050491063092024009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9360487366994042061349339 14040731050491063092024009)
              ·
                refine ⟨10530548287868297319018007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14040731050491063092024009 10530548287868297319018007)
                ·
                  refine ⟨15795822431802445978527011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10530548287868297319018007 15795822431802445978527011)
                  ·
                    refine ⟨23693733647703668967790517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15795822431802445978527011 23693733647703668967790517)
                    ·
                      refine ⟨2221287529472218965730361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23693733647703668967790517 2221287529472218965730361)
                      ·
                        rfl

theorem cell23_4325942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4325942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325942 prefixEnd_4325942 := by exact prefixLift 4325942
  have htrace : WordTrace (prefixWord ++ tailWord_4325942) baseStart_4325942 baseEnd_4325942 := by
    simpa [prefixWord, tailWord_4325942, baseEnd_4325942] using wordTrace_append hprefix tailTrace_4325942
  have hstable : (prefixWord ++ tailWord_4325942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325942).length < 2 ^ (prefixWord ++ tailWord_4325942).sum := by decide
  have hdescent : baseEnd_4325942 < baseStart_4325942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325949 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_4325949 : Nat := 118140960795 + 4325949 * 2 ^ 59
def prefixEnd_4325949 : Nat := 4983230072969 + 3 ^ 40 * 4325949 * 2
def baseEnd_4325949 : Nat := 740430374612266812780943

theorem tailTrace_4325949 : CollatzResearch.WordTrace tailWord_4325949 prefixEnd_4325949 740430374612266812780943 := by
  unfold tailWord_4325949
  simp only [CollatzResearch.WordTrace]
  refine ⟨157780322204833061114380901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105186881469888707409587267 157780322204833061114380901)
  ·
    refine ⟨29583810413406198958946419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157780322204833061114380901 29583810413406198958946419)
    ·
      refine ⟨44375715620109298438419629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29583810413406198958946419 44375715620109298438419629)
      ·
        refine ⟨16640893357540986914407361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44375715620109298438419629 16640893357540986914407361)
        ·
          refine ⟨12480670018155740185805521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16640893357540986914407361 12480670018155740185805521)
          ·
            refine ⟨9360502513616805139354141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12480670018155740185805521 9360502513616805139354141)
            ·
              refine ⟨3510188442606301927257803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9360502513616805139354141 3510188442606301927257803)
              ·
                refine ⟨5265282663909452890886705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510188442606301927257803 5265282663909452890886705)
                ·
                  refine ⟨3948961997932089668165029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5265282663909452890886705 3948961997932089668165029)
                  ·
                    refine ⟨740430374612266812780943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3948961997932089668165029 740430374612266812780943)
                    ·
                      rfl

theorem cell23_4325949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_4325949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325949 prefixEnd_4325949 := by exact prefixLift 4325949
  have htrace : WordTrace (prefixWord ++ tailWord_4325949) baseStart_4325949 baseEnd_4325949 := by
    simpa [prefixWord, tailWord_4325949, baseEnd_4325949] using wordTrace_append hprefix tailTrace_4325949
  have hstable : (prefixWord ++ tailWord_4325949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325949).length < 2 ^ (prefixWord ++ tailWord_4325949).sum := by decide
  have hdescent : baseEnd_4325949 < baseStart_4325949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325972 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_4325972 : Nat := 118140960795 + 4325972 * 2 ^ 59
def prefixEnd_4325972 : Nat := 4983230072969 + 3 ^ 40 * 4325972 * 2
def baseEnd_4325972 : Nat := 2221302933891853848355223

theorem tailTrace_4325972 : CollatzResearch.WordTrace tailWord_4325972 prefixEnd_4325972 2221302933891853848355223 := by
  unfold tailWord_4325972
  simp only [CollatzResearch.WordTrace]
  refine ⟨78890580541874868021234085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105187440722499824028312113 78890580541874868021234085)
  ·
    refine ⟨14791983851601537753981391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78890580541874868021234085 14791983851601537753981391)
    ·
      refine ⟨22187975777402306630972087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14791983851601537753981391 22187975777402306630972087)
      ·
        refine ⟨33281963666103459946458131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22187975777402306630972087 33281963666103459946458131)
        ·
          refine ⟨49922945499155189919687197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33281963666103459946458131 49922945499155189919687197)
          ·
            refine ⟨18721104562183196219882699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49922945499155189919687197 18721104562183196219882699)
            ·
              refine ⟨28081656843274794329824049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18721104562183196219882699 28081656843274794329824049)
              ·
                refine ⟨21061242632456095747368037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28081656843274794329824049 21061242632456095747368037)
                ·
                  refine ⟨3948982993585517952631507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21061242632456095747368037 3948982993585517952631507)
                  ·
                    refine ⟨5923474490378276928947261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3948982993585517952631507 5923474490378276928947261)
                    ·
                      refine ⟨2221302933891853848355223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5923474490378276928947261 2221302933891853848355223)
                      ·
                        rfl

theorem cell23_4325972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_4325972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325972 prefixEnd_4325972 := by exact prefixLift 4325972
  have htrace : WordTrace (prefixWord ++ tailWord_4325972) baseStart_4325972 baseEnd_4325972 := by
    simpa [prefixWord, tailWord_4325972, baseEnd_4325972] using wordTrace_append hprefix tailTrace_4325972
  have hstable : (prefixWord ++ tailWord_4325972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325972).length < 2 ^ (prefixWord ++ tailWord_4325972).sum := by decide
  have hdescent : baseEnd_4325972 < baseStart_4325972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325978 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_4325978 : Nat := 118140960795 + 4325978 * 2 ^ 59
def prefixEnd_4325978 : Nat := 4983230072969 + 3 ^ 40 * 4325978 * 2
def baseEnd_4325978 : Nat := 2221306014775780824880195

theorem tailTrace_4325978 : CollatzResearch.WordTrace tailWord_4325978 prefixEnd_4325978 2221306014775780824880195 := by
  unfold tailWord_4325978
  simp only [CollatzResearch.WordTrace]
  refine ⟨39445344980431999766796647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105187586614485332711457725 39445344980431999766796647)
  ·
    refine ⟨59168017470647999650194971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39445344980431999766796647 59168017470647999650194971)
    ·
      refine ⟨88752026205971999475292457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59168017470647999650194971 88752026205971999475292457)
      ·
        refine ⟨66564019654478999606469343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88752026205971999475292457 66564019654478999606469343)
        ·
          refine ⟨99846029481718499409704015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66564019654478999606469343 99846029481718499409704015)
          ·
            refine ⟨149769044222577749114556023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99846029481718499409704015 149769044222577749114556023)
            ·
              refine ⟨224653566333866623671834035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149769044222577749114556023 224653566333866623671834035)
              ·
                refine ⟨336980349500799935507751053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224653566333866623671834035 336980349500799935507751053)
                ·
                  refine ⟨126367631062799975815406645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336980349500799935507751053 126367631062799975815406645)
                  ·
                    refine ⟨11846965412137497732694373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 126367631062799975815406645 11846965412137497732694373)
                    ·
                      refine ⟨2221306014775780824880195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11846965412137497732694373 2221306014775780824880195)
                      ·
                        rfl

theorem cell23_4325978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_4325978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325978 prefixEnd_4325978 := by exact prefixLift 4325978
  have htrace : WordTrace (prefixWord ++ tailWord_4325978) baseStart_4325978 baseEnd_4325978 := by
    simpa [prefixWord, tailWord_4325978, baseEnd_4325978] using wordTrace_append hprefix tailTrace_4325978
  have hstable : (prefixWord ++ tailWord_4325978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325978).length < 2 ^ (prefixWord ++ tailWord_4325978).sum := by decide
  have hdescent : baseEnd_4325978 < baseStart_4325978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4325995 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 5, 4, 2]
def baseStart_4325995 : Nat := 118140960795 + 4325995 * 2 ^ 59
def prefixEnd_4325995 : Nat := 4983230072969 + 3 ^ 40 * 4325995 * 2
def baseEnd_4325995 : Nat := 2221314743946907258367617

theorem tailTrace_4325995 : CollatzResearch.WordTrace tailWord_4325995 prefixEnd_4325995 2221314743946907258367617 := by
  unfold tailWord_4325995
  simp only [CollatzResearch.WordTrace]
  refine ⟨157781999962666410970555439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105187999975110940647036959 157781999962666410970555439)
  ·
    refine ⟨236672999943999616455833159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157781999962666410970555439 236672999943999616455833159)
    ·
      refine ⟨355009499915999424683749739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236672999943999616455833159 355009499915999424683749739)
      ·
        refine ⟨532514249873999137025624609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355009499915999424683749739 532514249873999137025624609)
        ·
          refine ⟨399385687405499352769218457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532514249873999137025624609 399385687405499352769218457)
          ·
            refine ⟨299539265554124514576913843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399385687405499352769218457 299539265554124514576913843)
            ·
              refine ⟨449308898331186771865370765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299539265554124514576913843 449308898331186771865370765)
              ·
                refine ⟨168490836874195039449514037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449308898331186771865370765 168490836874195039449514037)
                ·
                  refine ⟨15796015956955784948391941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168490836874195039449514037 15796015956955784948391941)
                  ·
                    refine ⟨2961752991929209677823489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15796015956955784948391941 2961752991929209677823489)
                    ·
                      refine ⟨2221314743946907258367617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961752991929209677823489 2221314743946907258367617)
                      ·
                        rfl

theorem cell23_4325995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 4, 2].length) (baseStart_4325995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4325995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4325995 prefixEnd_4325995 := by exact prefixLift 4325995
  have htrace : WordTrace (prefixWord ++ tailWord_4325995) baseStart_4325995 baseEnd_4325995 := by
    simpa [prefixWord, tailWord_4325995, baseEnd_4325995] using wordTrace_append hprefix tailTrace_4325995
  have hstable : (prefixWord ++ tailWord_4325995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4325995).length < 2 ^ (prefixWord ++ tailWord_4325995).sum := by decide
  have hdescent : baseEnd_4325995 < baseStart_4325995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4325995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326006 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4326006 : Nat := 118140960795 + 4326006 * 2 ^ 59
def prefixEnd_4326006 : Nat := 4983230072969 + 3 ^ 40 * 4326006 * 2
def baseEnd_4326006 : Nat := 2221320392234106715330067

theorem tailTrace_4326006 : CollatzResearch.WordTrace tailWord_4326006 prefixEnd_4326006 2221320392234106715330067 := by
  unfold tailWord_4326006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861400072851659990575367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105188267443751039899470581 9861400072851659990575367)
  ·
    refine ⟨14792100109277489985863051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9861400072851659990575367 14792100109277489985863051)
    ·
      refine ⟨22188150163916234978794577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14792100109277489985863051 22188150163916234978794577)
      ·
        refine ⟨16641112622937176234095933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22188150163916234978794577 16641112622937176234095933)
        ·
          refine ⟨6240417233601441087785975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16641112622937176234095933 6240417233601441087785975)
          ·
            refine ⟨9360625850402161631678963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6240417233601441087785975 9360625850402161631678963)
            ·
              refine ⟨14040938775603242447518445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9360625850402161631678963 14040938775603242447518445)
              ·
                refine ⟨5265352040851215917819417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14040938775603242447518445 5265352040851215917819417)
                ·
                  refine ⟨3949014030638411938364563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5265352040851215917819417 3949014030638411938364563)
                  ·
                    refine ⟨5923521045957617907546845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3949014030638411938364563 5923521045957617907546845)
                    ·
                      refine ⟨2221320392234106715330067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5923521045957617907546845 2221320392234106715330067)
                      ·
                        rfl

theorem cell23_4326006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4326006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326006 prefixEnd_4326006 := by exact prefixLift 4326006
  have htrace : WordTrace (prefixWord ++ tailWord_4326006) baseStart_4326006 baseEnd_4326006 := by
    simpa [prefixWord, tailWord_4326006, baseEnd_4326006] using wordTrace_append hprefix tailTrace_4326006
  have hstable : (prefixWord ++ tailWord_4326006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326006).length < 2 ^ (prefixWord ++ tailWord_4326006).sum := by decide
  have hdescent : baseEnd_4326006 < baseStart_4326006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326028 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_4326028 : Nat := 118140960795 + 4326028 * 2 ^ 59
def prefixEnd_4326028 : Nat := 4983230072969 + 3 ^ 40 * 4326028 * 2
def baseEnd_4326028 : Nat := 2221331688808505629254965

theorem tailTrace_4326028 : CollatzResearch.WordTrace tailWord_4326028 prefixEnd_4326028 2221331688808505629254965 := by
  unfold tailWord_4326028
  simp only [CollatzResearch.WordTrace]
  refine ⟨78891601785773428803253369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105188802381031238404337825 78891601785773428803253369)
  ·
    refine ⟨59168701339330071602440027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78891601785773428803253369 59168701339330071602440027)
    ·
      refine ⟨88753052008995107403660041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59168701339330071602440027 88753052008995107403660041)
      ·
        refine ⟨66564789006746330552745031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88753052008995107403660041 66564789006746330552745031)
        ·
          refine ⟨99847183510119495829117547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66564789006746330552745031 99847183510119495829117547)
          ·
            refine ⟨149770775265179243743676321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99847183510119495829117547 149770775265179243743676321)
            ·
              refine ⟨112328081448884432807757241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149770775265179243743676321 112328081448884432807757241)
              ·
                refine ⟨84246061086663324605817931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112328081448884432807757241 84246061086663324605817931)
                ·
                  refine ⟨126369091629994986908726897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84246061086663324605817931 126369091629994986908726897)
                  ·
                    refine ⟨94776818722496240181545173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126369091629994986908726897 94776818722496240181545173)
                    ·
                      refine ⟨2221331688808505629254965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94776818722496240181545173 2221331688808505629254965)
                      ·
                        rfl

theorem cell23_4326028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_4326028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326028 prefixEnd_4326028 := by exact prefixLift 4326028
  have htrace : WordTrace (prefixWord ++ tailWord_4326028) baseStart_4326028 baseEnd_4326028 := by
    simpa [prefixWord, tailWord_4326028, baseEnd_4326028] using wordTrace_append hprefix tailTrace_4326028
  have hstable : (prefixWord ++ tailWord_4326028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326028).length < 2 ^ (prefixWord ++ tailWord_4326028).sum := by decide
  have hdescent : baseEnd_4326028 < baseStart_4326028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326052 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 5]
def baseStart_4326052 : Nat := 118140960795 + 4326052 * 2 ^ 59
def prefixEnd_4326052 : Nat := 4983230072969 + 3 ^ 40 * 4326052 * 2
def baseEnd_4326052 : Nat := 246816001371579281706095

theorem tailTrace_4326052 : CollatzResearch.WordTrace tailWord_4326052 prefixEnd_4326052 246816001371579281706095 := by
  unfold tailWord_4326052
  simp only [CollatzResearch.WordTrace]
  refine ⟨78892039461729954852690205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105189385948973273136920273 78892039461729954852690205)
  ·
    refine ⟨29584514798148733069758827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78892039461729954852690205 29584514798148733069758827)
    ·
      refine ⟨44376772197223099604638241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29584514798148733069758827 44376772197223099604638241)
      ·
        refine ⟨33282579147917324703478681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44376772197223099604638241 33282579147917324703478681)
        ·
          refine ⟨24961934360937993527609011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33282579147917324703478681 24961934360937993527609011)
          ·
            refine ⟨37442901541406990291413517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24961934360937993527609011 37442901541406990291413517)
            ·
              refine ⟨14041088078027621359280069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37442901541406990291413517 14041088078027621359280069)
              ·
                refine ⟨2632704014630179004865013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14041088078027621359280069 2632704014630179004865013)
                ·
                  refine ⟨246816001371579281706095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632704014630179004865013 246816001371579281706095)
                  ·
                    rfl

theorem cell23_4326052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_4326052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326052 prefixEnd_4326052 := by exact prefixLift 4326052
  have htrace : WordTrace (prefixWord ++ tailWord_4326052) baseStart_4326052 baseEnd_4326052 := by
    simpa [prefixWord, tailWord_4326052, baseEnd_4326052] using wordTrace_append hprefix tailTrace_4326052
  have hstable : (prefixWord ++ tailWord_4326052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326052).length < 2 ^ (prefixWord ++ tailWord_4326052).sum := by decide
  have hdescent : baseEnd_4326052 < baseStart_4326052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326135 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_4326135 : Nat := 118140960795 + 4326135 * 2 ^ 59
def prefixEnd_4326135 : Nat := 4983230072969 + 3 ^ 40 * 4326135 * 2
def baseEnd_4326135 : Nat := 2221386631238536710616973

theorem tailTrace_4326135 : CollatzResearch.WordTrace tailWord_4326135 prefixEnd_4326135 2221386631238536710616973 := by
  unfold tailWord_4326135
  simp only [CollatzResearch.WordTrace]
  refine ⟨157787106182159214880651859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105191404121439476587101239 157787106182159214880651859)
  ·
    refine ⟨236680659273238822320977789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157787106182159214880651859 236680659273238822320977789)
    ·
      refine ⟨88755247227464558370366671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236680659273238822320977789 88755247227464558370366671)
      ·
        refine ⟨133132870841196837555550007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88755247227464558370366671 133132870841196837555550007)
        ·
          refine ⟨199699306261795256333325011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133132870841196837555550007 199699306261795256333325011)
          ·
            refine ⟨299548959392692884499987517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199699306261795256333325011 299548959392692884499987517)
            ·
              refine ⟨112330859772259831687495319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299548959392692884499987517 112330859772259831687495319)
              ·
                refine ⟨168496289658389747531242979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112330859772259831687495319 168496289658389747531242979)
                ·
                  refine ⟨252744434487584621296864469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168496289658389747531242979 252744434487584621296864469)
                  ·
                    refine ⟨5923697683302764561645261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 252744434487584621296864469 5923697683302764561645261)
                    ·
                      refine ⟨2221386631238536710616973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5923697683302764561645261 2221386631238536710616973)
                      ·
                        rfl

theorem cell23_4326135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_4326135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326135 prefixEnd_4326135 := by exact prefixLift 4326135
  have htrace : WordTrace (prefixWord ++ tailWord_4326135) baseStart_4326135 baseEnd_4326135 := by
    simpa [prefixWord, tailWord_4326135, baseEnd_4326135] using wordTrace_append hprefix tailTrace_4326135
  have hstable : (prefixWord ++ tailWord_4326135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326135).length < 2 ^ (prefixWord ++ tailWord_4326135).sum := by decide
  have hdescent : baseEnd_4326135 < baseStart_4326135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326142 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_4326142 : Nat := 118140960795 + 4326142 * 2 ^ 59
def prefixEnd_4326142 : Nat := 4983230072969 + 3 ^ 40 * 4326142 * 2
def baseEnd_4326142 : Nat := 246821136178124242581049

theorem tailTrace_4326142 : CollatzResearch.WordTrace tailWord_4326142 prefixEnd_4326142 246821136178124242581049 := by
  unfold tailWord_4326142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19723420186641731884519585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105191574328755903384104453 19723420186641731884519585)
  ·
    refine ⟨14792565139981298913389689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19723420186641731884519585 14792565139981298913389689)
    ·
      refine ⟨11094423854985974185042267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14792565139981298913389689 11094423854985974185042267)
      ·
        refine ⟨16641635782478961277563401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11094423854985974185042267 16641635782478961277563401)
        ·
          refine ⟨12481226836859220958172551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16641635782478961277563401 12481226836859220958172551)
          ·
            refine ⟨18721840255288831437258827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12481226836859220958172551 18721840255288831437258827)
            ·
              refine ⟨28082760382933247155888241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18721840255288831437258827 28082760382933247155888241)
              ·
                refine ⟨21062070287199935366916181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28082760382933247155888241 21062070287199935366916181)
                ·
                  refine ⟨246821136178124242581049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21062070287199935366916181 246821136178124242581049)
                  ·
                    rfl

theorem cell23_4326142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_4326142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326142 prefixEnd_4326142 := by exact prefixLift 4326142
  have htrace : WordTrace (prefixWord ++ tailWord_4326142) baseStart_4326142 baseEnd_4326142 := by
    simpa [prefixWord, tailWord_4326142, baseEnd_4326142] using wordTrace_append hprefix tailTrace_4326142
  have hstable : (prefixWord ++ tailWord_4326142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326142).length < 2 ^ (prefixWord ++ tailWord_4326142).sum := by decide
  have hdescent : baseEnd_4326142 < baseStart_4326142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326155 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 5, 5]
def baseStart_4326155 : Nat := 118140960795 + 4326155 * 2 ^ 59
def prefixEnd_4326155 : Nat := 4983230072969 + 3 ^ 40 * 4326155 * 2
def baseEnd_4326155 : Nat := 740465633617208877455627

theorem tailTrace_4326155 : CollatzResearch.WordTrace tailWord_4326155 prefixEnd_4326155 740465633617208877455627 := by
  unfold tailWord_4326155
  simp only [CollatzResearch.WordTrace]
  refine ⟨157787835642086758296379919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105191890428057838864253279 157787835642086758296379919)
  ·
    refine ⟨236681753463130137444569879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157787835642086758296379919 236681753463130137444569879)
    ·
      refine ⟨355022630194695206166854819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236681753463130137444569879 355022630194695206166854819)
      ·
        refine ⟨532533945292042809250282229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355022630194695206166854819 532533945292042809250282229)
        ·
          refine ⟨49925057371129013367213959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 532533945292042809250282229 49925057371129013367213959)
          ·
            refine ⟨74887586056693520050820939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49925057371129013367213959 74887586056693520050820939)
            ·
              refine ⟨112331379085040280076231409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74887586056693520050820939 112331379085040280076231409)
              ·
                refine ⟨84248534313780210057173557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112331379085040280076231409 84248534313780210057173557)
                ·
                  refine ⟨7898300091916894692860021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84248534313780210057173557 7898300091916894692860021)
                  ·
                    refine ⟨740465633617208877455627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7898300091916894692860021 740465633617208877455627)
                    ·
                      rfl

theorem cell23_4326155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 5].length) (baseStart_4326155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326155 prefixEnd_4326155 := by exact prefixLift 4326155
  have htrace : WordTrace (prefixWord ++ tailWord_4326155) baseStart_4326155 baseEnd_4326155 := by
    simpa [prefixWord, tailWord_4326155, baseEnd_4326155] using wordTrace_append hprefix tailTrace_4326155
  have hstable : (prefixWord ++ tailWord_4326155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326155).length < 2 ^ (prefixWord ++ tailWord_4326155).sum := by decide
  have hdescent : baseEnd_4326155 < baseStart_4326155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326192 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 2, 6, 2]
def baseStart_4326192 : Nat := 118140960795 + 4326192 * 2 ^ 59
def prefixEnd_4326192 : Nat := 4983230072969 + 3 ^ 40 * 4326192 * 2
def baseEnd_4326192 : Nat := 2221415899635842987604211

theorem tailTrace_4326192 : CollatzResearch.WordTrace tailWord_4326192 prefixEnd_4326192 2221415899635842987604211 := by
  unfold tailWord_4326192
  simp only [CollatzResearch.WordTrace]
  refine ⟨78894592571476356807738415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105192790095301809076984553 78894592571476356807738415)
  ·
    refine ⟨118341888857214535211607623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78894592571476356807738415 118341888857214535211607623)
    ·
      refine ⟨177512833285821802817411435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118341888857214535211607623 177512833285821802817411435)
      ·
        refine ⟨266269249928732704226117153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177512833285821802817411435 266269249928732704226117153)
        ·
          refine ⟨199701937446549528169587865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266269249928732704226117153 199701937446549528169587865)
          ·
            refine ⟨149776453084912146127190899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199701937446549528169587865 149776453084912146127190899)
            ·
              refine ⟨224664679627368219190786349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149776453084912146127190899 224664679627368219190786349)
              ·
                refine ⟨84249254860263082196544881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224664679627368219190786349 84249254860263082196544881)
                ·
                  refine ⟨63186941145197311647408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84249254860263082196544881 63186941145197311647408661)
                  ·
                    refine ⟨2961887866181123983472281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63186941145197311647408661 2961887866181123983472281)
                    ·
                      refine ⟨2221415899635842987604211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961887866181123983472281 2221415899635842987604211)
                      ·
                        rfl

theorem cell23_4326192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2, 6, 2].length) (baseStart_4326192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326192 prefixEnd_4326192 := by exact prefixLift 4326192
  have htrace : WordTrace (prefixWord ++ tailWord_4326192) baseStart_4326192 baseEnd_4326192 := by
    simpa [prefixWord, tailWord_4326192, baseEnd_4326192] using wordTrace_append hprefix tailTrace_4326192
  have hstable : (prefixWord ++ tailWord_4326192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326192).length < 2 ^ (prefixWord ++ tailWord_4326192).sum := by decide
  have hdescent : baseEnd_4326192 < baseStart_4326192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326214 : List Nat := [6, 1, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4326214 : Nat := 118140960795 + 4326214 * 2 ^ 59
def prefixEnd_4326214 : Nat := 4983230072969 + 3 ^ 40 * 4326214 * 2
def baseEnd_4326214 : Nat := 740475732070080633843037

theorem tailTrace_4326214 : CollatzResearch.WordTrace tailWord_4326214 prefixEnd_4326214 740475732070080633843037 := by
  unfold tailWord_4326214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930937110902281605399303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105193325032582007581851797 4930937110902281605399303)
  ·
    refine ⟨7396405666353422408098955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4930937110902281605399303 7396405666353422408098955)
    ·
      refine ⟨11094608499530133612148433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7396405666353422408098955 11094608499530133612148433)
      ·
        refine ⟨8320956374647600209111325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11094608499530133612148433 8320956374647600209111325)
        ·
          refine ⟨3120358640492850078416747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8320956374647600209111325 3120358640492850078416747)
          ·
            refine ⟨4680537960739275117625121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120358640492850078416747 4680537960739275117625121)
            ·
              refine ⟨3510403470554456338218841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680537960739275117625121 3510403470554456338218841)
              ·
                refine ⟨2632802602915842253664131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510403470554456338218841 2632802602915842253664131)
                ·
                  refine ⟨3949203904373763380496197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632802602915842253664131 3949203904373763380496197)
                  ·
                    refine ⟨740475732070080633843037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949203904373763380496197 740475732070080633843037)
                    ·
                      rfl

theorem cell23_4326214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4326214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326214 prefixEnd_4326214 := by exact prefixLift 4326214
  have htrace : WordTrace (prefixWord ++ tailWord_4326214) baseStart_4326214 baseEnd_4326214 := by
    simpa [prefixWord, tailWord_4326214, baseEnd_4326214] using wordTrace_append hprefix tailTrace_4326214
  have hstable : (prefixWord ++ tailWord_4326214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326214).length < 2 ^ (prefixWord ++ tailWord_4326214).sum := by decide
  have hdescent : baseEnd_4326214 < baseStart_4326214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326220 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4326220 : Nat := 118140960795 + 4326220 * 2 ^ 59
def prefixEnd_4326220 : Nat := 4983230072969 + 3 ^ 40 * 4326220 * 2
def baseEnd_4326220 : Nat := 2221430277094168878054083

theorem tailTrace_4326220 : CollatzResearch.WordTrace tailWord_4326220 prefixEnd_4326220 2221430277094168878054083 := by
  unfold tailWord_4326220
  simp only [CollatzResearch.WordTrace]
  refine ⟨78895103193425637198748057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105193470924567516264997409 78895103193425637198748057)
  ·
    refine ⟨59171327395069227899061043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78895103193425637198748057 59171327395069227899061043)
    ·
      refine ⟨88756991092603841848591565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59171327395069227899061043 88756991092603841848591565)
      ·
        refine ⟨33283871659726440693221837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88756991092603841848591565 33283871659726440693221837)
        ·
          refine ⟨12481451872397415259958189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33283871659726440693221837 12481451872397415259958189)
          ·
            refine ⟨4680544452149030722484321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12481451872397415259958189 4680544452149030722484321)
            ·
              refine ⟨3510408339111773041863241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680544452149030722484321 3510408339111773041863241)
              ·
                refine ⟨2632806254333829781397431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510408339111773041863241 2632806254333829781397431)
                ·
                  refine ⟨3949209381500744672096147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632806254333829781397431 3949209381500744672096147)
                  ·
                    refine ⟨5923814072251117008144221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3949209381500744672096147 5923814072251117008144221)
                    ·
                      refine ⟨2221430277094168878054083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5923814072251117008144221 2221430277094168878054083)
                      ·
                        rfl

theorem cell23_4326220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4326220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326220 prefixEnd_4326220 := by exact prefixLift 4326220
  have htrace : WordTrace (prefixWord ++ tailWord_4326220) baseStart_4326220 baseEnd_4326220 := by
    simpa [prefixWord, tailWord_4326220, baseEnd_4326220] using wordTrace_append hprefix tailTrace_4326220
  have hstable : (prefixWord ++ tailWord_4326220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326220).length < 2 ^ (prefixWord ++ tailWord_4326220).sum := by decide
  have hdescent : baseEnd_4326220 < baseStart_4326220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326226 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_4326226 : Nat := 118140960795 + 4326226 * 2 ^ 59
def prefixEnd_4326226 : Nat := 4983230072969 + 3 ^ 40 * 4326226 * 2
def baseEnd_4326226 : Nat := 2221433357978095854579055

theorem tailTrace_4326226 : CollatzResearch.WordTrace tailWord_4326226 prefixEnd_4326226 2221433357978095854579055 := by
  unfold tailWord_4326226
  simp only [CollatzResearch.WordTrace]
  refine ⟨39447606306207384355553633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105193616816553024948143021 39447606306207384355553633)
  ·
    refine ⟨29585704729655538266665225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39447606306207384355553633 29585704729655538266665225)
    ·
      refine ⟨22189278547241653699998919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29585704729655538266665225 22189278547241653699998919)
      ·
        refine ⟨33283917820862480549998379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22189278547241653699998919 33283917820862480549998379)
        ·
          refine ⟨49925876731293720824997569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33283917820862480549998379 49925876731293720824997569)
          ·
            refine ⟨37444407548470290618748177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49925876731293720824997569 37444407548470290618748177)
            ·
              refine ⟨28083305661352717964061133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37444407548470290618748177 28083305661352717964061133)
              ·
                refine ⟨10531239623007269236522925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28083305661352717964061133 10531239623007269236522925)
                ·
                  refine ⟨3949214858627725963696097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10531239623007269236522925 3949214858627725963696097)
                  ·
                    refine ⟨2961911143970794472772073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949214858627725963696097 2961911143970794472772073)
                    ·
                      refine ⟨2221433357978095854579055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961911143970794472772073 2221433357978095854579055)
                      ·
                        rfl

theorem cell23_4326226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_4326226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326226 prefixEnd_4326226 := by exact prefixLift 4326226
  have htrace : WordTrace (prefixWord ++ tailWord_4326226) baseStart_4326226 baseEnd_4326226 := by
    simpa [prefixWord, tailWord_4326226, baseEnd_4326226] using wordTrace_append hprefix tailTrace_4326226
  have hstable : (prefixWord ++ tailWord_4326226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326226).length < 2 ^ (prefixWord ++ tailWord_4326226).sum := by decide
  have hdescent : baseEnd_4326226 < baseStart_4326226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326236 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4326236 : Nat := 118140960795 + 4326236 * 2 ^ 59
def prefixEnd_4326236 : Nat := 4983230072969 + 3 ^ 40 * 4326236 * 2
def baseEnd_4326236 : Nat := 740479497594880271818003

theorem tailTrace_4326236 : CollatzResearch.WordTrace tailWord_4326236 prefixEnd_4326236 740479497594880271818003 := by
  unfold tailWord_4326236
  simp only [CollatzResearch.WordTrace]
  refine ⟨78895394977396654565039281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105193859969862206086719041 78895394977396654565039281)
  ·
    refine ⟨59171546233047490923779461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78895394977396654565039281 59171546233047490923779461)
    ·
      refine ⟨11094664918696404548208649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59171546233047490923779461 11094664918696404548208649)
      ·
        refine ⟨8320998689022303411156487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11094664918696404548208649 8320998689022303411156487)
        ·
          refine ⟨12481498033533455116734731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8320998689022303411156487 12481498033533455116734731)
          ·
            refine ⟨18722247050300182675102097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12481498033533455116734731 18722247050300182675102097)
            ·
              refine ⟨14041685287725137006326573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18722247050300182675102097 14041685287725137006326573)
              ·
                refine ⟨5265631982896926377372465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14041685287725137006326573 5265631982896926377372465)
                ·
                  refine ⟨3949223987172694783029349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5265631982896926377372465 3949223987172694783029349)
                  ·
                    refine ⟨740479497594880271818003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949223987172694783029349 740479497594880271818003)
                    ·
                      rfl

theorem cell23_4326236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4326236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326236 prefixEnd_4326236 := by exact prefixLift 4326236
  have htrace : WordTrace (prefixWord ++ tailWord_4326236) baseStart_4326236 baseEnd_4326236 := by
    simpa [prefixWord, tailWord_4326236, baseEnd_4326236] using wordTrace_append hprefix tailTrace_4326236
  have hstable : (prefixWord ++ tailWord_4326236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326236).length < 2 ^ (prefixWord ++ tailWord_4326236).sum := by decide
  have hdescent : baseEnd_4326236 < baseStart_4326236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326270 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4326270 : Nat := 118140960795 + 4326270 * 2 ^ 59
def prefixEnd_4326270 : Nat := 4983230072969 + 3 ^ 40 * 4326270 * 2
def baseEnd_4326270 : Nat := 740485317042297894142951

theorem tailTrace_4326270 : CollatzResearch.WordTrace tailWord_4326270 prefixEnd_4326270 740485317042297894142951 := by
  unfold tailWord_4326270
  simp only [CollatzResearch.WordTrace]
  refine ⟨19724003754583766617102033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105194686691113421957877509 19724003754583766617102033)
  ·
    refine ⟨14793002815937824962826525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19724003754583766617102033 14793002815937824962826525)
    ·
      refine ⟨5547376055976684361059947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14793002815937824962826525 5547376055976684361059947)
      ·
        refine ⟨8321064083965026541589921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5547376055976684361059947 8321064083965026541589921)
        ·
          refine ⟨6240798062973769906192441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8321064083965026541589921 6240798062973769906192441)
          ·
            refine ⟨4680598547230327429644331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6240798062973769906192441 4680598547230327429644331)
            ·
              refine ⟨7020897820845491144466497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4680598547230327429644331 7020897820845491144466497)
              ·
                refine ⟨5265673365634118358349873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7020897820845491144466497 5265673365634118358349873)
                ·
                  refine ⟨3949255024225588768762405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5265673365634118358349873 3949255024225588768762405)
                  ·
                    refine ⟨740485317042297894142951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949255024225588768762405 740485317042297894142951)
                    ·
                      rfl

theorem cell23_4326270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4326270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326270 prefixEnd_4326270 := by exact prefixLift 4326270
  have htrace : WordTrace (prefixWord ++ tailWord_4326270) baseStart_4326270 baseEnd_4326270 := by
    simpa [prefixWord, tailWord_4326270, baseEnd_4326270] using wordTrace_append hprefix tailTrace_4326270
  have hstable : (prefixWord ++ tailWord_4326270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326270).length < 2 ^ (prefixWord ++ tailWord_4326270).sum := by decide
  have hdescent : baseEnd_4326270 < baseStart_4326270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326293 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_4326293 : Nat := 118140960795 + 4326293 * 2 ^ 59
def prefixEnd_4326293 : Nat := 4983230072969 + 3 ^ 40 * 4326293 * 2
def baseEnd_4326293 : Nat := 2221467761181947092441247

theorem tailTrace_4326293 : CollatzResearch.WordTrace tailWord_4326293 prefixEnd_4326293 2221467761181947092441247 := by
  unfold tailWord_4326293
  simp only [CollatzResearch.WordTrace]
  refine ⟨157792868915586807864903533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105195245943724538576602355 157792868915586807864903533)
  ·
    refine ⟨59172325843345052949338825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157792868915586807864903533 59172325843345052949338825)
    ·
      refine ⟨44379244382508789712004119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59172325843345052949338825 44379244382508789712004119)
      ·
        refine ⟨66568866573763184568006179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44379244382508789712004119 66568866573763184568006179)
        ·
          refine ⟨99853299860644776852009269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66568866573763184568006179 99853299860644776852009269)
          ·
            refine ⟨9361246861935447829875869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99853299860644776852009269 9361246861935447829875869)
            ·
              refine ⟨3510467573225792936203451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9361246861935447829875869 3510467573225792936203451)
              ·
                refine ⟨5265701359838689404305177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510467573225792936203451 5265701359838689404305177)
                ·
                  refine ⟨3949276019879017053228883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5265701359838689404305177 3949276019879017053228883)
                  ·
                    refine ⟨5923914029818525579843325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3949276019879017053228883 5923914029818525579843325)
                    ·
                      refine ⟨2221467761181947092441247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5923914029818525579843325 2221467761181947092441247)
                      ·
                        rfl

theorem cell23_4326293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_4326293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326293 prefixEnd_4326293 := by exact prefixLift 4326293
  have htrace : WordTrace (prefixWord ++ tailWord_4326293) baseStart_4326293 baseEnd_4326293 := by
    simpa [prefixWord, tailWord_4326293, baseEnd_4326293] using wordTrace_append hprefix tailTrace_4326293
  have hstable : (prefixWord ++ tailWord_4326293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326293).length < 2 ^ (prefixWord ++ tailWord_4326293).sum := by decide
  have hdescent : baseEnd_4326293 < baseStart_4326293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326303 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4326303 : Nat := 118140960795 + 4326303 * 2 ^ 59
def prefixEnd_4326303 : Nat := 4983230072969 + 3 ^ 40 * 4326303 * 2
def baseEnd_4326303 : Nat := 2221472895988492053316201

theorem tailTrace_4326303 : CollatzResearch.WordTrace tailWord_4326303 prefixEnd_4326303 2221472895988492053316201 := by
  unfold tailWord_4326303
  simp only [CollatzResearch.WordTrace]
  refine ⟨157793233645550579572767563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105195489097033719715178375 157793233645550579572767563)
  ·
    refine ⟨236689850468325869359151345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157793233645550579572767563 236689850468325869359151345)
    ·
      refine ⟨177517387851244402019363509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236689850468325869359151345 177517387851244402019363509)
      ·
        refine ⟨16642255111054162689315329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177517387851244402019363509 16642255111054162689315329)
        ·
          refine ⟨12481691333290622016986497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16642255111054162689315329 12481691333290622016986497)
          ·
            refine ⟨9361268499967966512739873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12481691333290622016986497 9361268499967966512739873)
            ·
              refine ⟨7020951374975974884554905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9361268499967966512739873 7020951374975974884554905)
              ·
                refine ⟨5265713531231981163416179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7020951374975974884554905 5265713531231981163416179)
                ·
                  refine ⟨7898570296847971745124269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5265713531231981163416179 7898570296847971745124269)
                  ·
                    refine ⟨2961963861317989404421601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7898570296847971745124269 2961963861317989404421601)
                    ·
                      refine ⟨2221472895988492053316201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961963861317989404421601 2221472895988492053316201)
                      ·
                        rfl

theorem cell23_4326303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4326303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326303 prefixEnd_4326303 := by exact prefixLift 4326303
  have htrace : WordTrace (prefixWord ++ tailWord_4326303) baseStart_4326303 baseEnd_4326303 := by
    simpa [prefixWord, tailWord_4326303, baseEnd_4326303] using wordTrace_append hprefix tailTrace_4326303
  have hstable : (prefixWord ++ tailWord_4326303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326303).length < 2 ^ (prefixWord ++ tailWord_4326303).sum := by decide
  have hdescent : baseEnd_4326303 < baseStart_4326303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326350 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_4326350 : Nat := 118140960795 + 4326350 * 2 ^ 59
def prefixEnd_4326350 : Nat := 4983230072969 + 3 ^ 40 * 4326350 * 2
def baseEnd_4326350 : Nat := 2221497029579253369428485

theorem tailTrace_4326350 : CollatzResearch.WordTrace tailWord_4326350 prefixEnd_4326350 2221497029579253369428485 := by
  unfold tailWord_4326350
  simp only [CollatzResearch.WordTrace]
  refine ⟨19724368484547538324966063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105196631917586871066485669 19724368484547538324966063)
  ·
    refine ⟨29586552726821307487449095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19724368484547538324966063 29586552726821307487449095)
    ·
      refine ⟨44379829090231961231173643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29586552726821307487449095 44379829090231961231173643)
      ·
        refine ⟨66569743635347941846760465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44379829090231961231173643 66569743635347941846760465)
        ·
          refine ⟨49927307726510956385070349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66569743635347941846760465 49927307726510956385070349)
          ·
            refine ⟨18722740397441608644401381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49927307726510956385070349 18722740397441608644401381)
            ·
              refine ⟨3510513824520301620825259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18722740397441608644401381 3510513824520301620825259)
              ·
                refine ⟨5265770736780452431237889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510513824520301620825259 5265770736780452431237889)
                ·
                  refine ⟨3949328052585339323428417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5265770736780452431237889 3949328052585339323428417)
                  ·
                    refine ⟨2961996039439004492571313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949328052585339323428417 2961996039439004492571313)
                    ·
                      refine ⟨2221497029579253369428485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2961996039439004492571313 2221497029579253369428485)
                      ·
                        rfl

theorem cell23_4326350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_4326350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326350 prefixEnd_4326350 := by exact prefixLift 4326350
  have htrace : WordTrace (prefixWord ++ tailWord_4326350) baseStart_4326350 baseEnd_4326350 := by
    simpa [prefixWord, tailWord_4326350, baseEnd_4326350] using wordTrace_append hprefix tailTrace_4326350
  have hstable : (prefixWord ++ tailWord_4326350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326350).length < 2 ^ (prefixWord ++ tailWord_4326350).sum := by decide
  have hdescent : baseEnd_4326350 < baseStart_4326350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326352 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_4326352 : Nat := 118140960795 + 4326352 * 2 ^ 59
def prefixEnd_4326352 : Nat := 4983230072969 + 3 ^ 40 * 4326352 * 2
def baseEnd_4326352 : Nat := 740499352180187453867825

theorem tailTrace_4326352 : CollatzResearch.WordTrace tailWord_4326352 prefixEnd_4326352 740499352180187453867825 := by
  unfold tailWord_4326352
  simp only [CollatzResearch.WordTrace]
  refine ⟨78897510411186530470650655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105196680548248707294200873 78897510411186530470650655)
  ·
    refine ⟨118346265616779795705975983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78897510411186530470650655 118346265616779795705975983)
    ·
      refine ⟨177519398425169693558963975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118346265616779795705975983 177519398425169693558963975)
      ·
        refine ⟨266279097637754540338445963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177519398425169693558963975 266279097637754540338445963)
        ·
          refine ⟨399418646456631810507668945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266279097637754540338445963 399418646456631810507668945)
          ·
            refine ⟨299563984842473857880751709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399418646456631810507668945 299563984842473857880751709)
            ·
              refine ⟨112336494315927696705281891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299563984842473857880751709 112336494315927696705281891)
              ·
                refine ⟨168504741473891545057922837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112336494315927696705281891 168504741473891545057922837)
                ·
                  refine ⟨7898659756588666174590133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 168504741473891545057922837 7898659756588666174590133)
                  ·
                    refine ⟨740499352180187453867825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7898659756588666174590133 740499352180187453867825)
                    ·
                      rfl

theorem cell23_4326352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_4326352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326352 prefixEnd_4326352 := by exact prefixLift 4326352
  have htrace : WordTrace (prefixWord ++ tailWord_4326352) baseStart_4326352 baseEnd_4326352 := by
    simpa [prefixWord, tailWord_4326352, baseEnd_4326352] using wordTrace_append hprefix tailTrace_4326352
  have hstable : (prefixWord ++ tailWord_4326352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326352).length < 2 ^ (prefixWord ++ tailWord_4326352).sum := by decide
  have hdescent : baseEnd_4326352 < baseStart_4326352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326359 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 4, 5, 2]
def baseStart_4326359 : Nat := 118140960795 + 4326359 * 2 ^ 59
def prefixEnd_4326359 : Nat := 4983230072969 + 3 ^ 40 * 4326359 * 2
def baseEnd_4326359 : Nat := 2221501650905143834215943

theorem tailTrace_4326359 : CollatzResearch.WordTrace tailWord_4326359 prefixEnd_4326359 2221501650905143834215943 := by
  unfold tailWord_4326359
  simp only [CollatzResearch.WordTrace]
  refine ⟨157795276133347701136806131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105196850755565134091204087 157795276133347701136806131)
  ·
    refine ⟨236692914200021551705209197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157795276133347701136806131 236692914200021551705209197)
    ·
      refine ⟨88759842825008081889453449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236692914200021551705209197 88759842825008081889453449)
      ·
        refine ⟨66569882118756061417090087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88759842825008081889453449 66569882118756061417090087)
        ·
          refine ⟨99854823178134092125635131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66569882118756061417090087 99854823178134092125635131)
          ·
            refine ⟨149782234767201138188452697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99854823178134092125635131 149782234767201138188452697)
            ·
              refine ⟨112336676075400853641339523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149782234767201138188452697 112336676075400853641339523)
              ·
                refine ⟨168505014113101280462009285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112336676075400853641339523 168505014113101280462009285)
                ·
                  refine ⟨31594690146206490086626741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168505014113101280462009285 31594690146206490086626741)
                  ·
                    refine ⟨2962002201206858445621257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31594690146206490086626741 2962002201206858445621257)
                    ·
                      refine ⟨2221501650905143834215943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962002201206858445621257 2221501650905143834215943)
                      ·
                        rfl

theorem cell23_4326359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_4326359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326359 prefixEnd_4326359 := by exact prefixLift 4326359
  have htrace : WordTrace (prefixWord ++ tailWord_4326359) baseStart_4326359 baseEnd_4326359 := by
    simpa [prefixWord, tailWord_4326359, baseEnd_4326359] using wordTrace_append hprefix tailTrace_4326359
  have hstable : (prefixWord ++ tailWord_4326359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326359).length < 2 ^ (prefixWord ++ tailWord_4326359).sum := by decide
  have hdescent : baseEnd_4326359 < baseStart_4326359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326390 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_4326390 : Nat := 118140960795 + 4326390 * 2 ^ 59
def prefixEnd_4326390 : Nat := 4983230072969 + 3 ^ 40 * 4326390 * 2
def baseEnd_4326390 : Nat := 246835285422825912547589

theorem tailTrace_4326390 : CollatzResearch.WordTrace tailWord_4326390 prefixEnd_4326390 246835285422825912547589 := by
  unfold tailWord_4326390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9862275424764712089449039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105197604530823595620789749 9862275424764712089449039)
  ·
    refine ⟨14793413137147068134173559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9862275424764712089449039 14793413137147068134173559)
    ·
      refine ⟨22190119705720602201260339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14793413137147068134173559 22190119705720602201260339)
      ·
        refine ⟨33285179558580903301890509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22190119705720602201260339 33285179558580903301890509)
        ·
          refine ⟨12481942334467838738208941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33285179558580903301890509 12481942334467838738208941)
          ·
            refine ⟨4680728375425439526828353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12481942334467838738208941 4680728375425439526828353)
            ·
              refine ⟨3510546281569079645121265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680728375425439526828353 3510546281569079645121265)
              ·
                refine ⟨2632909711176809733840949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510546281569079645121265 2632909711176809733840949)
                ·
                  refine ⟨246835285422825912547589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632909711176809733840949 246835285422825912547589)
                  ·
                    rfl

theorem cell23_4326390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_4326390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326390 prefixEnd_4326390 := by exact prefixLift 4326390
  have htrace : WordTrace (prefixWord ++ tailWord_4326390) baseStart_4326390 baseEnd_4326390 := by
    simpa [prefixWord, tailWord_4326390, baseEnd_4326390] using wordTrace_append hprefix tailTrace_4326390
  have hstable : (prefixWord ++ tailWord_4326390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326390).length < 2 ^ (prefixWord ++ tailWord_4326390).sum := by decide
  have hdescent : baseEnd_4326390 < baseStart_4326390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326392 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_4326392 : Nat := 118140960795 + 4326392 * 2 ^ 59
def prefixEnd_4326392 : Nat := 4983230072969 + 3 ^ 40 * 4326392 * 2
def baseEnd_4326392 : Nat := 2221518595766742205103291

theorem tailTrace_4326392 : CollatzResearch.WordTrace tailWord_4326392 prefixEnd_4326392 2221518595766742205103291 := by
  unfold tailWord_4326392
  simp only [CollatzResearch.WordTrace]
  refine ⟨78898239871114073886378715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105197653161485431848504953 78898239871114073886378715)
  ·
    refine ⟨118347359806671110829568073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78898239871114073886378715 118347359806671110829568073)
    ·
      refine ⟨88760519855003333122176055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118347359806671110829568073 88760519855003333122176055)
      ·
        refine ⟨133140779782504999683264083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88760519855003333122176055 133140779782504999683264083)
        ·
          refine ⟨199711169673757499524896125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133140779782504999683264083 199711169673757499524896125)
          ·
            refine ⟨74891688627659062321836047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199711169673757499524896125 74891688627659062321836047)
            ·
              refine ⟨112337532941488593482754071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74891688627659062321836047 112337532941488593482754071)
              ·
                refine ⟨168506299412232890224131107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112337532941488593482754071 168506299412232890224131107)
                ·
                  refine ⟨252759449118349335336196661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168506299412232890224131107 252759449118349335336196661)
                  ·
                    refine ⟨23696198354845250187768437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 252759449118349335336196661 23696198354845250187768437)
                    ·
                      refine ⟨2221518595766742205103291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23696198354845250187768437 2221518595766742205103291)
                      ·
                        rfl

theorem cell23_4326392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_4326392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326392 prefixEnd_4326392 := by exact prefixLift 4326392
  have htrace : WordTrace (prefixWord ++ tailWord_4326392) baseStart_4326392 baseEnd_4326392 := by
    simpa [prefixWord, tailWord_4326392, baseEnd_4326392] using wordTrace_append hprefix tailTrace_4326392
  have hstable : (prefixWord ++ tailWord_4326392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326392).length < 2 ^ (prefixWord ++ tailWord_4326392).sum := by decide
  have hdescent : baseEnd_4326392 < baseStart_4326392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326409 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_4326409 : Nat := 118140960795 + 4326409 * 2 ^ 59
def prefixEnd_4326409 : Nat := 4983230072969 + 3 ^ 40 * 4326409 * 2
def baseEnd_4326409 : Nat := 2221527324937868638590713

theorem tailTrace_4326409 : CollatzResearch.WordTrace tailWord_4326409 prefixEnd_4326409 2221527324937868638590713 := by
  unfold tailWord_4326409
  simp only [CollatzResearch.WordTrace]
  refine ⟨157797099783166559676126281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105198066522111039784084187 157797099783166559676126281)
  ·
    refine ⟨118347824837374919757094711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157797099783166559676126281 118347824837374919757094711)
    ·
      refine ⟨177521737256062379635642067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118347824837374919757094711 177521737256062379635642067)
      ·
        refine ⟨266282605884093569453463101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177521737256062379635642067 266282605884093569453463101)
        ·
          refine ⟨99855977206535088545048663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266282605884093569453463101 99855977206535088545048663)
          ·
            refine ⟨149783965809802632817572995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99855977206535088545048663 149783965809802632817572995)
            ·
              refine ⟨224675948714703949226359493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149783965809802632817572995 224675948714703949226359493)
              ·
                refine ⟨42126740384006990479942405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224675948714703949226359493 42126740384006990479942405)
                ·
                  refine ⟨7898763822001310714989201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42126740384006990479942405 7898763822001310714989201)
                  ·
                    refine ⟨5924072866500983036241901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7898763822001310714989201 5924072866500983036241901)
                    ·
                      refine ⟨2221527324937868638590713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5924072866500983036241901 2221527324937868638590713)
                      ·
                        rfl

theorem cell23_4326409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_4326409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326409 prefixEnd_4326409 := by exact prefixLift 4326409
  have htrace : WordTrace (prefixWord ++ tailWord_4326409) baseStart_4326409 baseEnd_4326409 := by
    simpa [prefixWord, tailWord_4326409, baseEnd_4326409] using wordTrace_append hprefix tailTrace_4326409
  have hstable : (prefixWord ++ tailWord_4326409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326409).length < 2 ^ (prefixWord ++ tailWord_4326409).sum := by decide
  have hdescent : baseEnd_4326409 < baseStart_4326409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326423 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4326423 : Nat := 118140960795 + 4326423 * 2 ^ 59
def prefixEnd_4326423 : Nat := 4983230072969 + 3 ^ 40 * 4326423 * 2
def baseEnd_4326423 : Nat := 2221534513667031583815649

theorem tailTrace_4326423 : CollatzResearch.WordTrace tailWord_4326423 prefixEnd_4326423 2221534513667031583815649 := by
  unfold tailWord_4326423
  simp only [CollatzResearch.WordTrace]
  refine ⟨157797610405115840067135923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105198406936743893378090615 157797610405115840067135923)
  ·
    refine ⟨236696415607673760100703885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157797610405115840067135923 236696415607673760100703885)
    ·
      refine ⟨88761155852877660037763957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236696415607673760100703885 88761155852877660037763957)
      ·
        refine ⟨8321358361207280628540371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88761155852877660037763957 8321358361207280628540371)
        ·
          refine ⟨12482037541810920942810557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8321358361207280628540371 12482037541810920942810557)
          ·
            refine ⟨4680764078179095353553959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12482037541810920942810557 4680764078179095353553959)
            ·
              refine ⟨7021146117268643030330939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4680764078179095353553959 7021146117268643030330939)
              ·
                refine ⟨10531719175902964545496409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021146117268643030330939 10531719175902964545496409)
                ·
                  refine ⟨7898789381927223409122307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10531719175902964545496409 7898789381927223409122307)
                  ·
                    refine ⟨11848184072890835113683461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7898789381927223409122307 11848184072890835113683461)
                    ·
                      refine ⟨2221534513667031583815649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11848184072890835113683461 2221534513667031583815649)
                      ·
                        rfl

theorem cell23_4326423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4326423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326423 prefixEnd_4326423 := by exact prefixLift 4326423
  have htrace : WordTrace (prefixWord ++ tailWord_4326423) baseStart_4326423 baseEnd_4326423 := by
    simpa [prefixWord, tailWord_4326423, baseEnd_4326423] using wordTrace_append hprefix tailTrace_4326423
  have hstable : (prefixWord ++ tailWord_4326423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326423).length < 2 ^ (prefixWord ++ tailWord_4326423).sum := by decide
  have hdescent : baseEnd_4326423 < baseStart_4326423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326433 : List Nat := [1, 2, 3, 2, 3, 1, 1, 5, 1, 4]
def baseStart_4326433 : Nat := 118140960795 + 4326433 * 2 ^ 59
def prefixEnd_4326433 : Nat := 4983230072969 + 3 ^ 40 * 4326433 * 2
def baseEnd_4326433 : Nat := 740513216157858848230201

theorem tailTrace_4326433 : CollatzResearch.WordTrace tailWord_4326433 prefixEnd_4326433 740513216157858848230201 := by
  unfold tailWord_4326433
  simp only [CollatzResearch.WordTrace]
  refine ⟨157797975135079611774999953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105198650090053074516666635 157797975135079611774999953)
  ·
    refine ⟨118348481351309708831249965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157797975135079611774999953 118348481351309708831249965)
    ·
      refine ⟨44380680506741140811718737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118348481351309708831249965 44380680506741140811718737)
      ·
        refine ⟨33285510380055855608789053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44380680506741140811718737 33285510380055855608789053)
        ·
          refine ⟨12482066392520945853295895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33285510380055855608789053 12482066392520945853295895)
          ·
            refine ⟨18723099588781418779943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12482066392520945853295895 18723099588781418779943843)
            ·
              refine ⟨28084649383172128169915765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18723099588781418779943843 28084649383172128169915765)
              ·
                refine ⟨2632935879672387015929603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28084649383172128169915765 2632935879672387015929603)
                ·
                  refine ⟨3949403819508580523894405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2632935879672387015929603 3949403819508580523894405)
                  ·
                    refine ⟨740513216157858848230201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949403819508580523894405 740513216157858848230201)
                    ·
                      rfl

theorem cell23_4326433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_4326433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326433 prefixEnd_4326433 := by exact prefixLift 4326433
  have htrace : WordTrace (prefixWord ++ tailWord_4326433) baseStart_4326433 baseEnd_4326433 := by
    simpa [prefixWord, tailWord_4326433, baseEnd_4326433] using wordTrace_append hprefix tailTrace_4326433
  have hstable : (prefixWord ++ tailWord_4326433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326433).length < 2 ^ (prefixWord ++ tailWord_4326433).sum := by decide
  have hdescent : baseEnd_4326433 < baseStart_4326433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326496 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4]
def baseStart_4326496 : Nat := 118140960795 + 4326496 * 2 ^ 59
def prefixEnd_4326496 : Nat := 4983230072969 + 3 ^ 40 * 4326496 * 2
def baseEnd_4326496 : Nat := 2221571997754809798202813

theorem tailTrace_4326496 : CollatzResearch.WordTrace tailWord_4326496 prefixEnd_4326496 2221571997754809798202813 := by
  unfold tailWord_4326496
  simp only [CollatzResearch.WordTrace]
  refine ⟨78900136466925686767271671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105200181955900915689695561 78900136466925686767271671)
  ·
    refine ⟨118350204700388530150907507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78900136466925686767271671 118350204700388530150907507)
    ·
      refine ⟨177525307050582795226361261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118350204700388530150907507 177525307050582795226361261)
      ·
        refine ⟨66571990143968548209885473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177525307050582795226361261 66571990143968548209885473)
        ·
          refine ⟨49928992607976411157414105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66571990143968548209885473 49928992607976411157414105)
          ·
            refine ⟨37446744455982308368060579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49928992607976411157414105 37446744455982308368060579)
            ·
              refine ⟨56170116683973462552090869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37446744455982308368060579 56170116683973462552090869)
              ·
                refine ⟨5265948439122512114258519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56170116683973462552090869 5265948439122512114258519)
                ·
                  refine ⟨7898922658683768171387779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5265948439122512114258519 7898922658683768171387779)
                  ·
                    refine ⟨11848383988025652257081669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7898922658683768171387779 11848383988025652257081669)
                    ·
                      refine ⟨2221571997754809798202813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11848383988025652257081669 2221571997754809798202813)
                      ·
                        rfl

theorem cell23_4326496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_4326496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326496 prefixEnd_4326496 := by exact prefixLift 4326496
  have htrace : WordTrace (prefixWord ++ tailWord_4326496) baseStart_4326496 baseEnd_4326496 := by
    simpa [prefixWord, tailWord_4326496, baseEnd_4326496] using wordTrace_append hprefix tailTrace_4326496
  have hstable : (prefixWord ++ tailWord_4326496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326496).length < 2 ^ (prefixWord ++ tailWord_4326496).sum := by decide
  have hdescent : baseEnd_4326496 < baseStart_4326496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326513 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 3, 2, 2]
def baseStart_4326513 : Nat := 118140960795 + 4326513 * 2 ^ 59
def prefixEnd_4326513 : Nat := 4983230072969 + 3 ^ 40 * 4326513 * 2
def baseEnd_4326513 : Nat := 2221580726925936231690235

theorem tailTrace_4326513 : CollatzResearch.WordTrace tailWord_4326513 prefixEnd_4326513 2221580726925936231690235 := by
  unfold tailWord_4326513
  simp only [CollatzResearch.WordTrace]
  refine ⟨157800892974789785437912193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105200595316526523625274795 157800892974789785437912193)
  ·
    refine ⟨118350669731092339078434145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157800892974789785437912193 118350669731092339078434145)
    ·
      refine ⟨88763002298319254308825609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118350669731092339078434145 88763002298319254308825609)
      ·
        refine ⟨66572251723739440731619207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88763002298319254308825609 66572251723739440731619207)
        ·
          refine ⟨99858377585609161097428811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66572251723739440731619207 99858377585609161097428811)
          ·
            refine ⟨149787566378413741646143217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99858377585609161097428811 149787566378413741646143217)
            ·
              refine ⟨112340674783810306234607413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149787566378413741646143217 112340674783810306234607413)
              ·
                refine ⟨10531938260982216209494445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112340674783810306234607413 10531938260982216209494445)
                ·
                  refine ⟨3949476847868331078560417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10531938260982216209494445 3949476847868331078560417)
                  ·
                    refine ⟨2962107635901248308920313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949476847868331078560417 2962107635901248308920313)
                    ·
                      refine ⟨2221580726925936231690235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962107635901248308920313 2221580726925936231690235)
                      ·
                        rfl

theorem cell23_4326513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_4326513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326513 prefixEnd_4326513 := by exact prefixLift 4326513
  have htrace : WordTrace (prefixWord ++ tailWord_4326513) baseStart_4326513 baseEnd_4326513 := by
    simpa [prefixWord, tailWord_4326513, baseEnd_4326513] using wordTrace_append hprefix tailTrace_4326513
  have hstable : (prefixWord ++ tailWord_4326513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326513).length < 2 ^ (prefixWord ++ tailWord_4326513).sum := by decide
  have hdescent : baseEnd_4326513 < baseStart_4326513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326519 : List Nat := [1, 1, 3, 1, 1, 4, 4, 8]
def baseStart_4326519 : Nat := 118140960795 + 4326519 * 2 ^ 59
def prefixEnd_4326519 : Nat := 4983230072969 + 3 ^ 40 * 4326519 * 2
def baseEnd_4326519 : Nat := 82280881770735674378341

theorem tailTrace_4326519 : CollatzResearch.WordTrace tailWord_4326519 prefixEnd_4326519 82280881770735674378341 := by
  unfold tailWord_4326519
  simp only [CollatzResearch.WordTrace]
  refine ⟨157801111812768048462630611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105200741208512032308420407 157801111812768048462630611)
  ·
    refine ⟨236701667719152072693945917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157801111812768048462630611 236701667719152072693945917)
    ·
      refine ⟨88763125394682027260229719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236701667719152072693945917 88763125394682027260229719)
      ·
        refine ⟨133144688092023040890344579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88763125394682027260229719 133144688092023040890344579)
        ·
          refine ⟨199717032138034561335516869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133144688092023040890344579 199717032138034561335516869)
          ·
            refine ⟨37446943525881480250409413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199717032138034561335516869 37446943525881480250409413)
            ·
              refine ⟨7021301911102777546951765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37446943525881480250409413 7021301911102777546951765)
              ·
                refine ⟨82280881770735674378341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7021301911102777546951765 82280881770735674378341)
                ·
                  rfl

theorem cell23_4326519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 8].length) (baseStart_4326519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326519 prefixEnd_4326519 := by exact prefixLift 4326519
  have htrace : WordTrace (prefixWord ++ tailWord_4326519) baseStart_4326519 baseEnd_4326519 := by
    simpa [prefixWord, tailWord_4326519, baseEnd_4326519] using wordTrace_append hprefix tailTrace_4326519
  have hstable : (prefixWord ++ tailWord_4326519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326519).length < 2 ^ (prefixWord ++ tailWord_4326519).sum := by decide
  have hdescent : baseEnd_4326519 < baseStart_4326519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326533 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_4326533 : Nat := 118140960795 + 4326533 * 2 ^ 59
def prefixEnd_4326533 : Nat := 4983230072969 + 3 ^ 40 * 4326533 * 2
def baseEnd_4326533 : Nat := 2221590996539026153440143

theorem tailTrace_4326533 : CollatzResearch.WordTrace tailWord_4326533 prefixEnd_4326533 2221590996539026153440143 := by
  unfold tailWord_4326533
  simp only [CollatzResearch.WordTrace]
  refine ⟨157801622434717328853640253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105201081623144885902426835 157801622434717328853640253)
  ·
    refine ⟨59175608413018998320115095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157801622434717328853640253 59175608413018998320115095)
    ·
      refine ⟨88763412619528497480172643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59175608413018998320115095 88763412619528497480172643)
      ·
        refine ⟨133145118929292746220258965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88763412619528497480172643 133145118929292746220258965)
        ·
          refine ⟨6241177449810597479074639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133145118929292746220258965 6241177449810597479074639)
          ·
            refine ⟨9361766174715896218611959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6241177449810597479074639 9361766174715896218611959)
            ·
              refine ⟨14042649262073844327917939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9361766174715896218611959 14042649262073844327917939)
              ·
                refine ⟨21063973893110766491876909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14042649262073844327917939 21063973893110766491876909)
                ·
                  refine ⟨7898990209916537434453841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21063973893110766491876909 7898990209916537434453841)
                  ·
                    refine ⟨5924242657437403075840381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7898990209916537434453841 5924242657437403075840381)
                    ·
                      refine ⟨2221590996539026153440143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5924242657437403075840381 2221590996539026153440143)
                      ·
                        rfl

theorem cell23_4326533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_4326533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326533 prefixEnd_4326533 := by exact prefixLift 4326533
  have htrace : WordTrace (prefixWord ++ tailWord_4326533) baseStart_4326533 baseEnd_4326533 := by
    simpa [prefixWord, tailWord_4326533, baseEnd_4326533] using wordTrace_append hprefix tailTrace_4326533
  have hstable : (prefixWord ++ tailWord_4326533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326533).length < 2 ^ (prefixWord ++ tailWord_4326533).sum := by decide
  have hdescent : baseEnd_4326533 < baseStart_4326533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326564 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_4326564 : Nat := 118140960795 + 4326564 * 2 ^ 59
def prefixEnd_4326564 : Nat := 4983230072969 + 3 ^ 40 * 4326564 * 2
def baseEnd_4326564 : Nat := 2221606914439315532152501

theorem tailTrace_4326564 : CollatzResearch.WordTrace tailWord_4326564 prefixEnd_4326564 2221606914439315532152501 := by
  unfold tailWord_4326564
  simp only [CollatzResearch.WordTrace]
  refine ⟨78901376548802510574009373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105201835398403347432012497 78901376548802510574009373)
  ·
    refine ⟨29588016205800941465253515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78901376548802510574009373 29588016205800941465253515)
    ·
      refine ⟨44382024308701412197880273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29588016205800941465253515 44382024308701412197880273)
      ·
        refine ⟨33286518231526059148410205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44382024308701412197880273 33286518231526059148410205)
        ·
          refine ⟨12482444336822272180653827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33286518231526059148410205 12482444336822272180653827)
          ·
            refine ⟨18723666505233408270980741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12482444336822272180653827 18723666505233408270980741)
            ·
              refine ⟨3510687469731264050808889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18723666505233408270980741 3510687469731264050808889)
              ·
                refine ⟨2633015602298448038106667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510687469731264050808889 2633015602298448038106667)
                ·
                  refine ⟨3949523403447672057160001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633015602298448038106667 3949523403447672057160001)
                  ·
                    refine ⟨2962142552585754042870001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949523403447672057160001 2962142552585754042870001)
                    ·
                      refine ⟨2221606914439315532152501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962142552585754042870001 2221606914439315532152501)
                      ·
                        rfl

theorem cell23_4326564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_4326564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326564 prefixEnd_4326564 := by exact prefixLift 4326564
  have htrace : WordTrace (prefixWord ++ tailWord_4326564) baseStart_4326564 baseEnd_4326564 := by
    simpa [prefixWord, tailWord_4326564, baseEnd_4326564] using wordTrace_append hprefix tailTrace_4326564
  have hstable : (prefixWord ++ tailWord_4326564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326564).length < 2 ^ (prefixWord ++ tailWord_4326564).sum := by decide
  have hdescent : baseEnd_4326564 < baseStart_4326564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326579 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 8]
def baseStart_4326579 : Nat := 118140960795 + 4326579 * 2 ^ 59
def prefixEnd_4326579 : Nat := 4983230072969 + 3 ^ 40 * 4326579 * 2
def baseEnd_4326579 : Nat := 740538205549710991154977

theorem tailTrace_4326579 : CollatzResearch.WordTrace tailWord_4326579 prefixEnd_4326579 740538205549710991154977 := by
  unfold tailWord_4326579
  simp only [CollatzResearch.WordTrace]
  refine ⟨157803300192550678709814791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105202200128367119139876527 157803300192550678709814791)
  ·
    refine ⟨236704950288826018064722187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157803300192550678709814791 236704950288826018064722187)
    ·
      refine ⟨355057425433239027097083281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236704950288826018064722187 355057425433239027097083281)
      ·
        refine ⟨266293069074929270322812461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355057425433239027097083281 266293069074929270322812461)
        ·
          refine ⟨99859900903098476371054673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266293069074929270322812461 99859900903098476371054673)
          ·
            refine ⟨74894925677323857278291005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99859900903098476371054673 74894925677323857278291005)
            ·
              refine ⟨28085597128996446479359127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74894925677323857278291005 28085597128996446479359127)
              ·
                refine ⟨42128395693494669719038691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28085597128996446479359127 42128395693494669719038691)
                ·
                  refine ⟨63192593540242004578558037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42128395693494669719038691 63192593540242004578558037)
                  ·
                    refine ⟨740538205549710991154977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63192593540242004578558037 740538205549710991154977)
                    ·
                      rfl

theorem cell23_4326579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_4326579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326579 prefixEnd_4326579 := by exact prefixLift 4326579
  have htrace : WordTrace (prefixWord ++ tailWord_4326579) baseStart_4326579 baseEnd_4326579 := by
    simpa [prefixWord, tailWord_4326579, baseEnd_4326579] using wordTrace_append hprefix tailTrace_4326579
  have hstable : (prefixWord ++ tailWord_4326579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326579).length < 2 ^ (prefixWord ++ tailWord_4326579).sum := by decide
  have hdescent : baseEnd_4326579 < baseStart_4326579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326590 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_4326590 : Nat := 118140960795 + 4326590 * 2 ^ 59
def prefixEnd_4326590 : Nat := 4983230072969 + 3 ^ 40 * 4326590 * 2
def baseEnd_4326590 : Nat := 2221620264936332430427381

theorem tailTrace_4326590 : CollatzResearch.WordTrace tailWord_4326590 prefixEnd_4326590 2221620264936332430427381 := by
  unfold tailWord_4326590
  simp only [CollatzResearch.WordTrace]
  refine ⟨19725462674438853448558153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105202467597007218392310149 19725462674438853448558153)
  ·
    refine ⟨14794097005829140086418615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19725462674438853448558153 14794097005829140086418615)
    ·
      refine ⟨22191145508743710129627923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14794097005829140086418615 22191145508743710129627923)
      ·
        refine ⟨33286718263115565194441885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22191145508743710129627923 33286718263115565194441885)
        ·
          refine ⟨12482519348668336947915707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33286718263115565194441885 12482519348668336947915707)
          ·
            refine ⟨18723779023002505421873561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12482519348668336947915707 18723779023002505421873561)
            ·
              refine ⟨14042834267251879066405171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18723779023002505421873561 14042834267251879066405171)
              ·
                refine ⟨21064251400877818599607757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14042834267251879066405171 21064251400877818599607757)
                ·
                  refine ⟨7899094275329181974852909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21064251400877818599607757 7899094275329181974852909)
                  ·
                    refine ⟨2962160353248443240569841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7899094275329181974852909 2962160353248443240569841)
                    ·
                      refine ⟨2221620264936332430427381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962160353248443240569841 2221620264936332430427381)
                      ·
                        rfl

theorem cell23_4326590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_4326590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326590 prefixEnd_4326590 := by exact prefixLift 4326590
  have htrace : WordTrace (prefixWord ++ tailWord_4326590) baseStart_4326590 baseEnd_4326590 := by
    simpa [prefixWord, tailWord_4326590, baseEnd_4326590] using wordTrace_append hprefix tailTrace_4326590
  have hstable : (prefixWord ++ tailWord_4326590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326590).length < 2 ^ (prefixWord ++ tailWord_4326590).sum := by decide
  have hdescent : baseEnd_4326590 < baseStart_4326590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326598 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4326598 : Nat := 118140960795 + 4326598 * 2 ^ 59
def prefixEnd_4326598 : Nat := 4983230072969 + 3 ^ 40 * 4326598 * 2
def baseEnd_4326598 : Nat := 2221624372781568399127345

theorem tailTrace_4326598 : CollatzResearch.WordTrace tailWord_4326598 prefixEnd_4326598 2221624372781568399127345 := by
  unfold tailWord_4326598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931374786858807654836139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105202662119654563303170965 4931374786858807654836139)
  ·
    refine ⟨7397062180288211482254209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4931374786858807654836139 7397062180288211482254209)
    ·
      refine ⟨5547796635216158611690657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7397062180288211482254209 5547796635216158611690657)
      ·
        refine ⟨4160847476412118958767993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5547796635216158611690657 4160847476412118958767993)
        ·
          refine ⟨3120635607309089219075995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4160847476412118958767993 3120635607309089219075995)
          ·
            refine ⟨4680953410963633828613993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120635607309089219075995 4680953410963633828613993)
            ·
              refine ⟨3510715058222725371460495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4680953410963633828613993 3510715058222725371460495)
              ·
                refine ⟨5266072587334088057190743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510715058222725371460495 5266072587334088057190743)
                ·
                  refine ⟨7899108881001132085786115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5266072587334088057190743 7899108881001132085786115)
                  ·
                    refine ⟨11848663321501698128679173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7899108881001132085786115 11848663321501698128679173)
                    ·
                      refine ⟨2221624372781568399127345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11848663321501698128679173 2221624372781568399127345)
                      ·
                        rfl

theorem cell23_4326598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4326598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326598 prefixEnd_4326598 := by exact prefixLift 4326598
  have htrace : WordTrace (prefixWord ++ tailWord_4326598) baseStart_4326598 baseEnd_4326598 := by
    simpa [prefixWord, tailWord_4326598, baseEnd_4326598] using wordTrace_append hprefix tailTrace_4326598
  have hstable : (prefixWord ++ tailWord_4326598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326598).length < 2 ^ (prefixWord ++ tailWord_4326598).sum := by decide
  have hdescent : baseEnd_4326598 < baseStart_4326598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326609 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 11]
def baseStart_4326609 : Nat := 118140960795 + 4326609 * 2 ^ 59
def prefixEnd_4326609 : Nat := 4983230072969 + 3 ^ 40 * 4326609 * 2
def baseEnd_4326609 : Nat := 246847780118751984009977

theorem tailTrace_4326609 : CollatzResearch.WordTrace tailWord_4326609 prefixEnd_4326609 246847780118751984009977 := by
  unfold tailWord_4326609
  simp only [CollatzResearch.WordTrace]
  refine ⟨157804394382441993833406881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105202929588294662555604587 157804394382441993833406881)
  ·
    refine ⟨118353295786831495375055161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157804394382441993833406881 118353295786831495375055161)
    ·
      refine ⟨88764971840123621531291371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118353295786831495375055161 88764971840123621531291371)
      ·
        refine ⟨133147457760185432296937057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88764971840123621531291371 133147457760185432296937057)
        ·
          refine ⟨99860593320139074222702793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133147457760185432296937057 99860593320139074222702793)
          ·
            refine ⟨74895444990104305667027095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99860593320139074222702793 74895444990104305667027095)
            ·
              refine ⟨112343167485156458500540643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74895444990104305667027095 112343167485156458500540643)
              ·
                refine ⟨168514751227734687750810965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112343167485156458500540643 168514751227734687750810965)
                ·
                  refine ⟨246847780118751984009977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 168514751227734687750810965 246847780118751984009977)
                  ·
                    rfl

theorem cell23_4326609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_4326609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326609 prefixEnd_4326609 := by exact prefixLift 4326609
  have htrace : WordTrace (prefixWord ++ tailWord_4326609) baseStart_4326609 baseEnd_4326609 := by
    simpa [prefixWord, tailWord_4326609, baseEnd_4326609] using wordTrace_append hprefix tailTrace_4326609
  have hstable : (prefixWord ++ tailWord_4326609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326609).length < 2 ^ (prefixWord ++ tailWord_4326609).sum := by decide
  have hdescent : baseEnd_4326609 < baseStart_4326609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326637 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4326637 : Nat := 118140960795 + 4326637 * 2 ^ 59
def prefixEnd_4326637 : Nat := 4983230072969 + 3 ^ 40 * 4326637 * 2
def baseEnd_4326637 : Nat := 2221644398527093746539665

theorem tailTrace_4326637 : CollatzResearch.WordTrace tailWord_4326637 prefixEnd_4326637 2221644398527093746539665 := by
  unfold tailWord_4326637
  simp only [CollatzResearch.WordTrace]
  refine ⟨157805415626340554615426165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105203610417560369743617443 157805415626340554615426165)
  ·
    refine ⟨14794257714969426995196203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157805415626340554615426165 14794257714969426995196203)
    ·
      refine ⟨22191386572454140492794305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14794257714969426995196203 22191386572454140492794305)
      ·
        refine ⟨16643539929340605369595729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22191386572454140492794305 16643539929340605369595729)
        ·
          refine ⟨12482654947005454027196797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16643539929340605369595729 12482654947005454027196797)
          ·
            refine ⟨4680995605127045260198799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12482654947005454027196797 4680995605127045260198799)
            ·
              refine ⟨7021493407690567890298199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4680995605127045260198799 7021493407690567890298199)
              ·
                refine ⟨10532240111535851835447299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021493407690567890298199 10532240111535851835447299)
                ·
                  refine ⟨15798360167303777753170949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10532240111535851835447299 15798360167303777753170949)
                  ·
                    refine ⟨2962192531369458328719553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15798360167303777753170949 2962192531369458328719553)
                    ·
                      refine ⟨2221644398527093746539665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962192531369458328719553 2221644398527093746539665)
                      ·
                        rfl

theorem cell23_4326637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4326637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326637 prefixEnd_4326637 := by exact prefixLift 4326637
  have htrace : WordTrace (prefixWord ++ tailWord_4326637) baseStart_4326637 baseEnd_4326637 := by
    simpa [prefixWord, tailWord_4326637, baseEnd_4326637] using wordTrace_append hprefix tailTrace_4326637
  have hstable : (prefixWord ++ tailWord_4326637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326637).length < 2 ^ (prefixWord ++ tailWord_4326637).sum := by decide
  have hdescent : baseEnd_4326637 < baseStart_4326637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326656 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_4326656 : Nat := 118140960795 + 4326656 * 2 ^ 59
def prefixEnd_4326656 : Nat := 4983230072969 + 3 ^ 40 * 4326656 * 2
def baseEnd_4326656 : Nat := 740551384886509724067359

theorem tailTrace_4326656 : CollatzResearch.WordTrace tailWord_4326656 prefixEnd_4326656 740551384886509724067359 := by
  unfold tailWord_4326656
  simp only [CollatzResearch.WordTrace]
  refine ⟨78903054306635860430183911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105204072408847813906911881 78903054306635860430183911)
  ·
    refine ⟨118354581459953790645275867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78903054306635860430183911 118354581459953790645275867)
    ·
      refine ⟨177531872189930685967913801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118354581459953790645275867 177531872189930685967913801)
      ·
        refine ⟨133148904142448014475935351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177531872189930685967913801 133148904142448014475935351)
        ·
          refine ⟨199723356213672021713903027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133148904142448014475935351 199723356213672021713903027)
          ·
            refine ⟨299585034320508032570854541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199723356213672021713903027 299585034320508032570854541)
            ·
              refine ⟨112344387870190512214070453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299585034320508032570854541 112344387870190512214070453)
              ·
                refine ⟨10532286362830360520069105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112344387870190512214070453 10532286362830360520069105)
                ·
                  refine ⟨7899214772122770390051829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10532286362830360520069105 7899214772122770390051829)
                  ·
                    refine ⟨740551384886509724067359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7899214772122770390051829 740551384886509724067359)
                    ·
                      rfl

theorem cell23_4326656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_4326656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326656 prefixEnd_4326656 := by exact prefixLift 4326656
  have htrace : WordTrace (prefixWord ++ tailWord_4326656) baseStart_4326656 baseEnd_4326656 := by
    simpa [prefixWord, tailWord_4326656, baseEnd_4326656] using wordTrace_append hprefix tailTrace_4326656
  have hstable : (prefixWord ++ tailWord_4326656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326656).length < 2 ^ (prefixWord ++ tailWord_4326656).sum := by decide
  have hdescent : baseEnd_4326656 < baseStart_4326656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326660 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 5]
def baseStart_4326660 : Nat := 118140960795 + 4326660 * 2 ^ 59
def prefixEnd_4326660 : Nat := 4983230072969 + 3 ^ 40 * 4326660 * 2
def baseEnd_4326660 : Nat := 246850689842460795172451

theorem tailTrace_4326660 : CollatzResearch.WordTrace tailWord_4326660 prefixEnd_4326660 246850689842460795172451 := by
  unfold tailWord_4326660
  simp only [CollatzResearch.WordTrace]
  refine ⟨78903127252628614771756717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105204169670171486362342289 78903127252628614771756717)
  ·
    refine ⟨29588672719735730539408769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78903127252628614771756717 29588672719735730539408769)
    ·
      refine ⟨22191504539801797904556577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29588672719735730539408769 22191504539801797904556577)
      ·
        refine ⟨16643628404851348428417433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22191504539801797904556577 16643628404851348428417433)
        ·
          refine ⟨12482721303638511321313075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16643628404851348428417433 12482721303638511321313075)
          ·
            refine ⟨18724081955457766981969613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12482721303638511321313075 18724081955457766981969613)
            ·
              refine ⟨7021530733296662618238605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18724081955457766981969613 7021530733296662618238605)
              ·
                refine ⟨2633074024986248481839477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7021530733296662618238605 2633074024986248481839477)
                ·
                  refine ⟨246850689842460795172451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2633074024986248481839477 246850689842460795172451)
                  ·
                    rfl

theorem cell23_4326660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_4326660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326660 prefixEnd_4326660 := by exact prefixLift 4326660
  have htrace : WordTrace (prefixWord ++ tailWord_4326660) baseStart_4326660 baseEnd_4326660 := by
    simpa [prefixWord, tailWord_4326660, baseEnd_4326660] using wordTrace_append hprefix tailTrace_4326660
  have hstable : (prefixWord ++ tailWord_4326660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326660).length < 2 ^ (prefixWord ++ tailWord_4326660).sum := by decide
  have hdescent : baseEnd_4326660 < baseStart_4326660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326666 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4326666 : Nat := 118140960795 + 4326666 * 2 ^ 59
def prefixEnd_4326666 : Nat := 4983230072969 + 3 ^ 40 * 4326666 * 2
def baseEnd_4326666 : Nat := 2221659289466074133077031

theorem tailTrace_4326666 : CollatzResearch.WordTrace tailWord_4326666 prefixEnd_4326666 2221659289466074133077031 := by
  unfold tailWord_4326666
  simp only [CollatzResearch.WordTrace]
  refine ⟨39451618335808873142057963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105204315562156995045487901 39451618335808873142057963)
  ·
    refine ⟨59177427503713309713086945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39451618335808873142057963 59177427503713309713086945)
    ·
      refine ⟨44383070627784982284815209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59177427503713309713086945 44383070627784982284815209)
      ·
        refine ⟨33287302970838736713611407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44383070627784982284815209 33287302970838736713611407)
        ·
          refine ⟨49930954456258105070417111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33287302970838736713611407 49930954456258105070417111)
          ·
            refine ⟨74896431684387157605625667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49930954456258105070417111 74896431684387157605625667)
            ·
              refine ⟨112344647526580736408438501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74896431684387157605625667 112344647526580736408438501)
              ·
                refine ⟨21064621411233888076582219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112344647526580736408438501 21064621411233888076582219)
                ·
                  refine ⟨31596932116850832114873329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21064621411233888076582219 31596932116850832114873329)
                  ·
                    refine ⟨23697699087638124086154997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31596932116850832114873329 23697699087638124086154997)
                    ·
                      refine ⟨2221659289466074133077031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23697699087638124086154997 2221659289466074133077031)
                      ·
                        rfl

theorem cell23_4326666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4326666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326666 prefixEnd_4326666 := by exact prefixLift 4326666
  have htrace : WordTrace (prefixWord ++ tailWord_4326666) baseStart_4326666 baseEnd_4326666 := by
    simpa [prefixWord, tailWord_4326666, baseEnd_4326666] using wordTrace_append hprefix tailTrace_4326666
  have hstable : (prefixWord ++ tailWord_4326666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326666).length < 2 ^ (prefixWord ++ tailWord_4326666).sum := by decide
  have hdescent : baseEnd_4326666 < baseStart_4326666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326720 : List Nat := [2, 1, 1, 2, 2, 1, 4, 5, 1, 4]
def baseStart_4326720 : Nat := 118140960795 + 4326720 * 2 ^ 59
def prefixEnd_4326720 : Nat := 4983230072969 + 3 ^ 40 * 4326720 * 2
def baseEnd_4326720 : Nat := 740562339140472307267261

theorem tailTrace_4326720 : CollatzResearch.WordTrace tailWord_4326720 prefixEnd_4326720 740562339140472307267261 := by
  unfold tailWord_4326720
  simp only [CollatzResearch.WordTrace]
  refine ⟨78904221442519929895348807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105205628590026573193798409 78904221442519929895348807)
  ·
    refine ⟨118356332163779894843023211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78904221442519929895348807 118356332163779894843023211)
    ·
      refine ⟨177534498245669842264534817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118356332163779894843023211 177534498245669842264534817)
      ·
        refine ⟨133150873684252381698401113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177534498245669842264534817 133150873684252381698401113)
        ·
          refine ⟨99863155263189286273800835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133150873684252381698401113 99863155263189286273800835)
          ·
            refine ⟨149794732894783929410701253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99863155263189286273800835 149794732894783929410701253)
            ·
              refine ⟨28086512417771986764506485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149794732894783929410701253 28086512417771986764506485)
              ·
                refine ⟨2633110539166123759172483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28086512417771986764506485 2633110539166123759172483)
                ·
                  refine ⟨3949665808749185638758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633110539166123759172483 3949665808749185638758725)
                  ·
                    refine ⟨740562339140472307267261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949665808749185638758725 740562339140472307267261)
                    ·
                      rfl

theorem cell23_4326720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 1, 4].length) (baseStart_4326720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326720 prefixEnd_4326720 := by exact prefixLift 4326720
  have htrace : WordTrace (prefixWord ++ tailWord_4326720) baseStart_4326720 baseEnd_4326720 := by
    simpa [prefixWord, tailWord_4326720, baseEnd_4326720] using wordTrace_append hprefix tailTrace_4326720
  have hstable : (prefixWord ++ tailWord_4326720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326720).length < 2 ^ (prefixWord ++ tailWord_4326720).sum := by decide
  have hdescent : baseEnd_4326720 < baseStart_4326720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326736 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_4326736 : Nat := 118140960795 + 4326736 * 2 ^ 59
def prefixEnd_4326736 : Nat := 4983230072969 + 3 ^ 40 * 4326736 * 2
def baseEnd_4326736 : Nat := 2221695233111888859201709

theorem tailTrace_4326736 : CollatzResearch.WordTrace tailWord_4326736 prefixEnd_4326736 2221695233111888859201709 := by
  unfold tailWord_4326736
  simp only [CollatzResearch.WordTrace]
  refine ⟨78904513226490947261640031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105206017635321263015520041 78904513226490947261640031)
  ·
    refine ⟨118356769839736420892460047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78904513226490947261640031 118356769839736420892460047)
    ·
      refine ⟨177535154759604631338690071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118356769839736420892460047 177535154759604631338690071)
      ·
        refine ⟨266302732139406947008035107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177535154759604631338690071 266302732139406947008035107)
        ·
          refine ⟨399454098209110420512052661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266302732139406947008035107 399454098209110420512052661)
          ·
            refine ⟨37448821707104101923004937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 399454098209110420512052661 37448821707104101923004937)
            ·
              refine ⟨28086616280328076442253703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37448821707104101923004937 28086616280328076442253703)
              ·
                refine ⟨42129924420492114663380555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28086616280328076442253703 42129924420492114663380555)
                ·
                  refine ⟨63194886630738171995070833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42129924420492114663380555 63194886630738171995070833)
                  ·
                    refine ⟨47396164973053628996303125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63194886630738171995070833 47396164973053628996303125)
                    ·
                      refine ⟨2221695233111888859201709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47396164973053628996303125 2221695233111888859201709)
                      ·
                        rfl

theorem cell23_4326736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_4326736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326736 prefixEnd_4326736 := by exact prefixLift 4326736
  have htrace : WordTrace (prefixWord ++ tailWord_4326736) baseStart_4326736 baseEnd_4326736 := by
    simpa [prefixWord, tailWord_4326736, baseEnd_4326736] using wordTrace_append hprefix tailTrace_4326736
  have hstable : (prefixWord ++ tailWord_4326736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326736).length < 2 ^ (prefixWord ++ tailWord_4326736).sum := by decide
  have hdescent : baseEnd_4326736 < baseStart_4326736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326770 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_4326770 : Nat := 118140960795 + 4326770 * 2 ^ 59
def prefixEnd_4326770 : Nat := 4983230072969 + 3 ^ 40 * 4326770 * 2
def baseEnd_4326770 : Nat := 2221712691454141726176553

theorem tailTrace_4326770 : CollatzResearch.WordTrace tailWord_4326770 prefixEnd_4326770 2221712691454141726176553 := by
  unfold tailWord_4326770
  simp only [CollatzResearch.WordTrace]
  refine ⟨39452566633714679582504441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105206844356572478886678509 39452566633714679582504441)
  ·
    refine ⟨29589424975286009686878331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39452566633714679582504441 29589424975286009686878331)
    ·
      refine ⟨44384137462929014530317497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29589424975286009686878331 44384137462929014530317497)
      ·
        refine ⟨33288103097196760897738123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44384137462929014530317497 33288103097196760897738123)
        ·
          refine ⟨49932154645795141346607185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33288103097196760897738123 49932154645795141346607185)
          ·
            refine ⟨37449115984346356009955389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49932154645795141346607185 37449115984346356009955389)
            ·
              refine ⟨14043418494129883503733271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37449115984346356009955389 14043418494129883503733271)
              ·
                refine ⟨21065127741194825255599907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14043418494129883503733271 21065127741194825255599907)
                ·
                  refine ⟨31597691611792237883399861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21065127741194825255599907 31597691611792237883399861)
                  ·
                    refine ⟨2962283588605522301568737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31597691611792237883399861 2962283588605522301568737)
                    ·
                      refine ⟨2221712691454141726176553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962283588605522301568737 2221712691454141726176553)
                      ·
                        rfl

theorem cell23_4326770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_4326770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326770 prefixEnd_4326770 := by exact prefixLift 4326770
  have htrace : WordTrace (prefixWord ++ tailWord_4326770) baseStart_4326770 baseEnd_4326770 := by
    simpa [prefixWord, tailWord_4326770, baseEnd_4326770] using wordTrace_append hprefix tailTrace_4326770
  have hstable : (prefixWord ++ tailWord_4326770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326770).length < 2 ^ (prefixWord ++ tailWord_4326770).sum := by decide
  have hdescent : baseEnd_4326770 < baseStart_4326770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326777 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 1, 1, 3]
def baseStart_4326777 : Nat := 118140960795 + 4326777 * 2 ^ 59
def prefixEnd_4326777 : Nat := 4983230072969 + 3 ^ 40 * 4326777 * 2
def baseEnd_4326777 : Nat := 2221716285818723198789021

theorem tailTrace_4326777 : CollatzResearch.WordTrace tailWord_4326777 prefixEnd_4326777 2221716285818723198789021 := by
  unfold tailWord_4326777
  simp only [CollatzResearch.WordTrace]
  refine ⟨157810521845833358525522585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105207014563888905683681723 157810521845833358525522585)
  ·
    refine ⟨118357891384375018894141939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157810521845833358525522585 118357891384375018894141939)
    ·
      refine ⟨177536837076562528341212909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118357891384375018894141939 177536837076562528341212909)
      ·
        refine ⟨66576313903710948127954841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177536837076562528341212909 66576313903710948127954841)
        ·
          refine ⟨49932235427783211095966131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66576313903710948127954841 49932235427783211095966131)
          ·
            refine ⟨74898353141674816643949197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49932235427783211095966131 74898353141674816643949197)
            ·
              refine ⟨28086882428128056241480949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74898353141674816643949197 28086882428128056241480949)
              ·
                refine ⟨2633145227637005272638839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28086882428128056241480949 2633145227637005272638839)
                ·
                  refine ⟨3949717841455507908958259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633145227637005272638839 3949717841455507908958259)
                  ·
                    refine ⟨5924576762183261863437389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3949717841455507908958259 5924576762183261863437389)
                    ·
                      refine ⟨2221716285818723198789021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5924576762183261863437389 2221716285818723198789021)
                      ·
                        rfl

theorem cell23_4326777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_4326777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326777 prefixEnd_4326777 := by exact prefixLift 4326777
  have htrace : WordTrace (prefixWord ++ tailWord_4326777) baseStart_4326777 baseEnd_4326777 := by
    simpa [prefixWord, tailWord_4326777, baseEnd_4326777] using wordTrace_append hprefix tailTrace_4326777
  have hstable : (prefixWord ++ tailWord_4326777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326777).length < 2 ^ (prefixWord ++ tailWord_4326777).sum := by decide
  have hdescent : baseEnd_4326777 < baseStart_4326777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326814 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4326814 : Nat := 118140960795 + 4326814 * 2 ^ 59
def prefixEnd_4326814 : Nat := 4983230072969 + 3 ^ 40 * 4326814 * 2
def baseEnd_4326814 : Nat := 740578428200979851342117

theorem tailTrace_4326814 : CollatzResearch.WordTrace tailWord_4326814 prefixEnd_4326814 740578428200979851342117 := by
  unfold tailWord_4326814
  simp only [CollatzResearch.WordTrace]
  refine ⟨19726483918337414230577437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105207914231132875896412997 19726483918337414230577437)
  ·
    refine ⟨7397431469376530336466539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19726483918337414230577437 7397431469376530336466539)
    ·
      refine ⟨11096147204064795504699809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7397431469376530336466539 11096147204064795504699809)
      ·
        refine ⟨8322110403048596628524857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11096147204064795504699809 8322110403048596628524857)
        ·
          refine ⟨6241582802286447471393643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8322110403048596628524857 6241582802286447471393643)
          ·
            refine ⟨9362374203429671207090465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6241582802286447471393643 9362374203429671207090465)
            ·
              refine ⟨7021780652572253405317849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9362374203429671207090465 7021780652572253405317849)
              ·
                refine ⟨5266335489429190053988387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7021780652572253405317849 5266335489429190053988387)
                ·
                  refine ⟨7899503234143785080982581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5266335489429190053988387 7899503234143785080982581)
                  ·
                    refine ⟨740578428200979851342117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7899503234143785080982581 740578428200979851342117)
                    ·
                      rfl

theorem cell23_4326814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4326814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326814 prefixEnd_4326814 := by exact prefixLift 4326814
  have htrace : WordTrace (prefixWord ++ tailWord_4326814) baseStart_4326814 baseEnd_4326814 := by
    simpa [prefixWord, tailWord_4326814, baseEnd_4326814] using wordTrace_append hprefix tailTrace_4326814
  have hstable : (prefixWord ++ tailWord_4326814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326814).length < 2 ^ (prefixWord ++ tailWord_4326814).sum := by decide
  have hdescent : baseEnd_4326814 < baseStart_4326814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326823 : List Nat := [1, 1, 6, 1, 1, 1, 3, 9]
def baseStart_4326823 : Nat := 118140960795 + 4326823 * 2 ^ 59
def prefixEnd_4326823 : Nat := 4983230072969 + 3 ^ 40 * 4326823 * 2
def baseEnd_4326823 : Nat := 82286663182549259956067

theorem tailTrace_4326823 : CollatzResearch.WordTrace tailWord_4326823 prefixEnd_4326823 82286663182549259956067 := by
  unfold tailWord_4326823
  simp only [CollatzResearch.WordTrace]
  refine ⟨157812199603666708381697123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105208133069111138921131415 157812199603666708381697123)
  ·
    refine ⟨236718299405500062572545685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157812199603666708381697123 236718299405500062572545685)
    ·
      refine ⟨11096170284632815433088079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 236718299405500062572545685 11096170284632815433088079)
      ·
        refine ⟨16644255426949223149632119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11096170284632815433088079 16644255426949223149632119)
        ·
          refine ⟨24966383140423834724448179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16644255426949223149632119 24966383140423834724448179)
          ·
            refine ⟨37449574710635752086672269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24966383140423834724448179 37449574710635752086672269)
            ·
              refine ⟨14043590516488407032502101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37449574710635752086672269 14043590516488407032502101)
              ·
                refine ⟨82286663182549259956067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14043590516488407032502101 82286663182549259956067)
                ·
                  rfl

theorem cell23_4326823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 9].length) (baseStart_4326823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326823 prefixEnd_4326823 := by exact prefixLift 4326823
  have htrace : WordTrace (prefixWord ++ tailWord_4326823) baseStart_4326823 baseEnd_4326823 := by
    simpa [prefixWord, tailWord_4326823, baseEnd_4326823] using wordTrace_append hprefix tailTrace_4326823
  have hstable : (prefixWord ++ tailWord_4326823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326823).length < 2 ^ (prefixWord ++ tailWord_4326823).sum := by decide
  have hdescent : baseEnd_4326823 < baseStart_4326823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326834 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_4326834 : Nat := 118140960795 + 4326834 * 2 ^ 59
def prefixEnd_4326834 : Nat := 4983230072969 + 3 ^ 40 * 4326834 * 2
def baseEnd_4326834 : Nat := 2221745554216029475776259

theorem tailTrace_4326834 : CollatzResearch.WordTrace tailWord_4326834 prefixEnd_4326834 2221745554216029475776259 := by
  unfold tailWord_4326834
  simp only [CollatzResearch.WordTrace]
  refine ⟨39453150201656714315086889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105208400537751238173565037 39453150201656714315086889)
  ·
    refine ⟨29589862651242535736315167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39453150201656714315086889 29589862651242535736315167)
    ·
      refine ⟨44384793976863803604472751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29589862651242535736315167 44384793976863803604472751)
      ·
        refine ⟨66577190965295705406709127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44384793976863803604472751 66577190965295705406709127)
        ·
          refine ⟨99865786447943558110063691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66577190965295705406709127 99865786447943558110063691)
          ·
            refine ⟨149798679671915337165095537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99865786447943558110063691 149798679671915337165095537)
            ·
              refine ⟨112349009753936502873821653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149798679671915337165095537 112349009753936502873821653)
              ·
                refine ⟨2633179916107886786105195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112349009753936502873821653 2633179916107886786105195)
                ·
                  refine ⟨3949769874161830179157793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633179916107886786105195 3949769874161830179157793)
                  ·
                    refine ⟨2962327405621372634368345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949769874161830179157793 2962327405621372634368345)
                    ·
                      refine ⟨2221745554216029475776259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962327405621372634368345 2221745554216029475776259)
                      ·
                        rfl

theorem cell23_4326834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_4326834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326834 prefixEnd_4326834 := by exact prefixLift 4326834
  have htrace : WordTrace (prefixWord ++ tailWord_4326834) baseStart_4326834 baseEnd_4326834 := by
    simpa [prefixWord, tailWord_4326834, baseEnd_4326834] using wordTrace_append hprefix tailTrace_4326834
  have hstable : (prefixWord ++ tailWord_4326834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326834).length < 2 ^ (prefixWord ++ tailWord_4326834).sum := by decide
  have hdescent : baseEnd_4326834 < baseStart_4326834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326837 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_4326837 : Nat := 118140960795 + 4326837 * 2 ^ 59
def prefixEnd_4326837 : Nat := 4983230072969 + 3 ^ 40 * 4326837 * 2
def baseEnd_4326837 : Nat := 2221747094657992964038745

theorem tailTrace_4326837 : CollatzResearch.WordTrace tailWord_4326837 prefixEnd_4326837 2221747094657992964038745 := by
  unfold tailWord_4326837
  simp only [CollatzResearch.WordTrace]
  refine ⟨157812710225615988772706765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105208473483743992515137843 157812710225615988772706765)
  ·
    refine ⟨59179766334605995789765037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157812710225615988772706765 59179766334605995789765037)
    ·
      refine ⟨22192412375477248421161889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59179766334605995789765037 22192412375477248421161889)
      ·
        refine ⟨16644309281607936315871417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22192412375477248421161889 16644309281607936315871417)
        ·
          refine ⟨12483231961205952236903563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16644309281607936315871417 12483231961205952236903563)
          ·
            refine ⟨18724847941808928355355345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12483231961205952236903563 18724847941808928355355345)
            ·
              refine ⟨14043635956356696266516509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18724847941808928355355345 14043635956356696266516509)
              ·
                refine ⟨5266363483633761099943691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14043635956356696266516509 5266363483633761099943691)
                ·
                  refine ⟨7899545225450641649915537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5266363483633761099943691 7899545225450641649915537)
                  ·
                    refine ⟨5924658919087981237436653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7899545225450641649915537 5924658919087981237436653)
                    ·
                      refine ⟨2221747094657992964038745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5924658919087981237436653 2221747094657992964038745)
                      ·
                        rfl

theorem cell23_4326837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_4326837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326837 prefixEnd_4326837 := by exact prefixLift 4326837
  have htrace : WordTrace (prefixWord ++ tailWord_4326837) baseStart_4326837 baseEnd_4326837 := by
    simpa [prefixWord, tailWord_4326837, baseEnd_4326837] using wordTrace_append hprefix tailTrace_4326837
  have hstable : (prefixWord ++ tailWord_4326837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326837).length < 2 ^ (prefixWord ++ tailWord_4326837).sum := by decide
  have hdescent : baseEnd_4326837 < baseStart_4326837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326901 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4326901 : Nat := 118140960795 + 4326901 * 2 ^ 59
def prefixEnd_4326901 : Nat := 4983230072969 + 3 ^ 40 * 4326901 * 2
def baseEnd_4326901 : Nat := 2221779957419880713638451

theorem tailTrace_4326901 : CollatzResearch.WordTrace tailWord_4326901 prefixEnd_4326901 2221779957419880713638451 := by
  unfold tailWord_4326901
  simp only [CollatzResearch.WordTrace]
  refine ⟨157815044497384127703036557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105210029664922751802024371 157815044497384127703036557)
  ·
    refine ⟨59180641686519047888638709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157815044497384127703036557 59180641686519047888638709)
    ·
      refine ⟨5548185158111160739559879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59180641686519047888638709 5548185158111160739559879)
      ·
        refine ⟨8322277737166741109339819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5548185158111160739559879 8322277737166741109339819)
        ·
          refine ⟨12483416605750111664009729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8322277737166741109339819 12483416605750111664009729)
          ·
            refine ⟨9362562454312583748007297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12483416605750111664009729 9362562454312583748007297)
            ·
              refine ⟨7021921840734437811005473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9362562454312583748007297 7021921840734437811005473)
              ·
                refine ⟨5266441380550828358254105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7021921840734437811005473 5266441380550828358254105)
                ·
                  refine ⟨3949831035413121268690579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5266441380550828358254105 3949831035413121268690579)
                  ·
                    refine ⟨5924746553119681903035869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3949831035413121268690579 5924746553119681903035869)
                    ·
                      refine ⟨2221779957419880713638451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5924746553119681903035869 2221779957419880713638451)
                      ·
                        rfl

theorem cell23_4326901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4326901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326901 prefixEnd_4326901 := by exact prefixLift 4326901
  have htrace : WordTrace (prefixWord ++ tailWord_4326901) baseStart_4326901 baseEnd_4326901 := by
    simpa [prefixWord, tailWord_4326901, baseEnd_4326901] using wordTrace_append hprefix tailTrace_4326901
  have hstable : (prefixWord ++ tailWord_4326901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326901).length < 2 ^ (prefixWord ++ tailWord_4326901).sum := by decide
  have hdescent : baseEnd_4326901 < baseStart_4326901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326918 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4326918 : Nat := 118140960795 + 4326918 * 2 ^ 59
def prefixEnd_4326918 : Nat := 4983230072969 + 3 ^ 40 * 4326918 * 2
def baseEnd_4326918 : Nat := 2221788686591007147125873

theorem tailTrace_4326918 : CollatzResearch.WordTrace tailWord_4326918 prefixEnd_4326918 2221788686591007147125873 := by
  unfold tailWord_4326918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931739516822579362700169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 105210443025548359737603605 4931739516822579362700169)
  ·
    refine ⟨3698804637616934522025127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4931739516822579362700169 3698804637616934522025127)
    ·
      refine ⟨5548206956425401783037691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698804637616934522025127 5548206956425401783037691)
      ·
        refine ⟨8322310434638102674556537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5548206956425401783037691 8322310434638102674556537)
        ·
          refine ⟨6241732825978577005917403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8322310434638102674556537 6241732825978577005917403)
          ·
            refine ⟨9362599238967865508876105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6241732825978577005917403 9362599238967865508876105)
            ·
              refine ⟨7021949429225899131657079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9362599238967865508876105 7021949429225899131657079)
              ·
                refine ⟨10532924143838848697485619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021949429225899131657079 10532924143838848697485619)
                ·
                  refine ⟨15799386215758273046228429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10532924143838848697485619 15799386215758273046228429)
                  ·
                    refine ⟨5924769830909352392335661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15799386215758273046228429 5924769830909352392335661)
                    ·
                      refine ⟨2221788686591007147125873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5924769830909352392335661 2221788686591007147125873)
                      ·
                        rfl

theorem cell23_4326918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4326918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326918 prefixEnd_4326918 := by exact prefixLift 4326918
  have htrace : WordTrace (prefixWord ++ tailWord_4326918) baseStart_4326918 baseEnd_4326918 := by
    simpa [prefixWord, tailWord_4326918, baseEnd_4326918] using wordTrace_append hprefix tailTrace_4326918
  have hstable : (prefixWord ++ tailWord_4326918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326918).length < 2 ^ (prefixWord ++ tailWord_4326918).sum := by decide
  have hdescent : baseEnd_4326918 < baseStart_4326918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326924 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 1, 4, 2]
def baseStart_4326924 : Nat := 118140960795 + 4326924 * 2 ^ 59
def prefixEnd_4326924 : Nat := 4983230072969 + 3 ^ 40 * 4326924 * 2
def baseEnd_4326924 : Nat := 2221791767474934123650845

theorem tailTrace_4326924 : CollatzResearch.WordTrace tailWord_4326924 prefixEnd_4326924 2221791767474934123650845 := by
  unfold tailWord_4326924
  simp only [CollatzResearch.WordTrace]
  refine ⟨78907941688150401315561913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105210588917533868420749217 78907941688150401315561913)
  ·
    refine ⟨59180956266112800986671435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78907941688150401315561913 59180956266112800986671435)
    ·
      refine ⟨88771434399169201480007153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59180956266112800986671435 88771434399169201480007153)
      ·
        refine ⟨66578575799376901110005365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88771434399169201480007153 66578575799376901110005365)
        ·
          refine ⟨6241741481191584479063003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66578575799376901110005365 6241741481191584479063003)
          ·
            refine ⟨9362612221787376718594505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6241741481191584479063003 9362612221787376718594505)
            ·
              refine ⟨7021959166340532538945879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9362612221787376718594505 7021959166340532538945879)
              ·
                refine ⟨10532938749510798808418819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7021959166340532538945879 10532938749510798808418819)
                ·
                  refine ⟨15799408124266198212628229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10532938749510798808418819 15799408124266198212628229)
                  ·
                    refine ⟨2962389023299912164867793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15799408124266198212628229 2962389023299912164867793)
                    ·
                      refine ⟨2221791767474934123650845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962389023299912164867793 2221791767474934123650845)
                      ·
                        rfl

theorem cell23_4326924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_4326924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326924 prefixEnd_4326924 := by exact prefixLift 4326924
  have htrace : WordTrace (prefixWord ++ tailWord_4326924) baseStart_4326924 baseEnd_4326924 := by
    simpa [prefixWord, tailWord_4326924, baseEnd_4326924] using wordTrace_append hprefix tailTrace_4326924
  have hstable : (prefixWord ++ tailWord_4326924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326924).length < 2 ^ (prefixWord ++ tailWord_4326924).sum := by decide
  have hdescent : baseEnd_4326924 < baseStart_4326924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326940 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4326940 : Nat := 118140960795 + 4326940 * 2 ^ 59
def prefixEnd_4326940 : Nat := 4983230072969 + 3 ^ 40 * 4326940 * 2
def baseEnd_4326940 : Nat := 2221799983165406061050771

theorem tailTrace_4326940 : CollatzResearch.WordTrace tailWord_4326940 prefixEnd_4326940 2221799983165406061050771 := by
  unfold tailWord_4326940
  simp only [CollatzResearch.WordTrace]
  refine ⟨78908233472121418681853137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105210977962828558242470849 78908233472121418681853137)
  ·
    refine ⟨59181175104091064011389853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78908233472121418681853137 59181175104091064011389853)
    ·
      refine ⟨22192940664034149004271195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59181175104091064011389853 22192940664034149004271195)
      ·
        refine ⟨33289410996051223506406793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22192940664034149004271195 33289410996051223506406793)
        ·
          refine ⟨24967058247038417629805095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33289410996051223506406793 24967058247038417629805095)
          ·
            refine ⟨37450587370557626444707643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24967058247038417629805095 37450587370557626444707643)
            ·
              refine ⟨56175881055836439667061465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37450587370557626444707643 56175881055836439667061465)
              ·
                refine ⟨42131910791877329750296099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56175881055836439667061465 42131910791877329750296099)
                ·
                  refine ⟨63197866187815994625444149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42131910791877329750296099 63197866187815994625444149)
                  ·
                    refine ⟨5924799955107749496135389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63197866187815994625444149 5924799955107749496135389)
                    ·
                      refine ⟨2221799983165406061050771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5924799955107749496135389 2221799983165406061050771)
                      ·
                        rfl

theorem cell23_4326940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4326940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326940 prefixEnd_4326940 := by exact prefixLift 4326940
  have htrace : WordTrace (prefixWord ++ tailWord_4326940) baseStart_4326940 baseEnd_4326940 := by
    simpa [prefixWord, tailWord_4326940, baseEnd_4326940] using wordTrace_append hprefix tailTrace_4326940
  have hstable : (prefixWord ++ tailWord_4326940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326940).length < 2 ^ (prefixWord ++ tailWord_4326940).sum := by decide
  have hdescent : baseEnd_4326940 < baseStart_4326940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4326958 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_4326958 : Nat := 118140960795 + 4326958 * 2 ^ 59
def prefixEnd_4326958 : Nat := 4983230072969 + 3 ^ 40 * 4326958 * 2
def baseEnd_4326958 : Nat := 2221809225817186990625689

theorem tailTrace_4326958 : CollatzResearch.WordTrace tailWord_4326958 prefixEnd_4326958 2221809225817186990625689 := by
  unfold tailWord_4326958
  simp only [CollatzResearch.WordTrace]
  refine ⟨19727140432272203304732691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105211415638785084291907685 19727140432272203304732691)
  ·
    refine ⟨29590710648408304957099037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19727140432272203304732691 29590710648408304957099037)
    ·
      refine ⟨11096516493153114358912139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29590710648408304957099037 11096516493153114358912139)
      ·
        refine ⟨16644774739729671538368209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11096516493153114358912139 16644774739729671538368209)
        ·
          refine ⟨12483581054797253653776157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16644774739729671538368209 12483581054797253653776157)
          ·
            refine ⟨4681342895548970120166059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12483581054797253653776157 4681342895548970120166059)
            ·
              refine ⟨7022014343323455180249089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681342895548970120166059 7022014343323455180249089)
              ·
                refine ⟨5266510757492591385186817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7022014343323455180249089 5266510757492591385186817)
                ·
                  refine ⟨3949883068119443538890113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5266510757492591385186817 3949883068119443538890113)
                  ·
                    refine ⟨2962412301089582654167585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3949883068119443538890113 2962412301089582654167585)
                    ·
                      refine ⟨2221809225817186990625689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962412301089582654167585 2221809225817186990625689)
                      ·
                        rfl

theorem cell23_4326958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_4326958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4326958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4326958 prefixEnd_4326958 := by exact prefixLift 4326958
  have htrace : WordTrace (prefixWord ++ tailWord_4326958) baseStart_4326958 baseEnd_4326958 := by
    simpa [prefixWord, tailWord_4326958, baseEnd_4326958] using wordTrace_append hprefix tailTrace_4326958
  have hstable : (prefixWord ++ tailWord_4326958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4326958).length < 2 ^ (prefixWord ++ tailWord_4326958).sum := by decide
  have hdescent : baseEnd_4326958 < baseStart_4326958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4326958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327020 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 6]
def baseStart_4327020 : Nat := 118140960795 + 4327020 * 2 ^ 59
def prefixEnd_4327020 : Nat := 4983230072969 + 3 ^ 40 * 4327020 * 2
def baseEnd_4327020 : Nat := 246871229068640638672267

theorem tailTrace_4327020 : CollatzResearch.WordTrace tailWord_4327020 prefixEnd_4327020 246871229068640638672267 := by
  unfold tailWord_4327020
  simp only [CollatzResearch.WordTrace]
  refine ⟨78909692391976505513309257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105212923189302007351079009 78909692391976505513309257)
  ·
    refine ⟨59182269293982379134981943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78909692391976505513309257 59182269293982379134981943)
    ·
      refine ⟨88773403940973568702472915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59182269293982379134981943 88773403940973568702472915)
      ·
        refine ⟨133160105911460353053709373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88773403940973568702472915 133160105911460353053709373)
        ·
          refine ⟨49935039716797632395141015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133160105911460353053709373 49935039716797632395141015)
          ·
            refine ⟨74902559575196448592711523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49935039716797632395141015 74902559575196448592711523)
            ·
              refine ⟨112353839362794672889067285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74902559575196448592711523 112353839362794672889067285)
              ·
                refine ⟨5266586220131000291675029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112353839362794672889067285 5266586220131000291675029)
                ·
                  refine ⟨246871229068640638672267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5266586220131000291675029 246871229068640638672267)
                  ·
                    rfl

theorem cell23_4327020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_4327020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327020 prefixEnd_4327020 := by exact prefixLift 4327020
  have htrace : WordTrace (prefixWord ++ tailWord_4327020) baseStart_4327020 baseEnd_4327020 := by
    simpa [prefixWord, tailWord_4327020, baseEnd_4327020] using wordTrace_append hprefix tailTrace_4327020
  have hstable : (prefixWord ++ tailWord_4327020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327020).length < 2 ^ (prefixWord ++ tailWord_4327020).sum := by decide
  have hdescent : baseEnd_4327020 < baseStart_4327020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327024 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 3, 4]
def baseStart_4327024 : Nat := 118140960795 + 4327024 * 2 ^ 59
def prefixEnd_4327024 : Nat := 4983230072969 + 3 ^ 40 * 4327024 * 2
def baseEnd_4327024 : Nat := 740614371846794577466795

theorem tailTrace_4327024 : CollatzResearch.WordTrace tailWord_4327024 prefixEnd_4327024 740614371846794577466795 := by
  unfold tailWord_4327024
  simp only [CollatzResearch.WordTrace]
  refine ⟨78909765337969259854882063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105213020450625679806509417 78909765337969259854882063)
  ·
    refine ⟨118364648006953889782323095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78909765337969259854882063 118364648006953889782323095)
    ·
      refine ⟨177546972010430834673484643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118364648006953889782323095 177546972010430834673484643)
      ·
        refine ⟨266320458015646252010226965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177546972010430834673484643 266320458015646252010226965)
        ·
          refine ⟨12483771469483418062979389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 266320458015646252010226965 12483771469483418062979389)
          ·
            refine ⟨4681414301056281773617271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12483771469483418062979389 4681414301056281773617271)
            ·
              refine ⟨7022121451584422660425907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681414301056281773617271 7022121451584422660425907)
              ·
                refine ⟨10533182177376633990638861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7022121451584422660425907 10533182177376633990638861)
                ·
                  refine ⟨3949943316516237746489573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10533182177376633990638861 3949943316516237746489573)
                  ·
                    refine ⟨740614371846794577466795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3949943316516237746489573 740614371846794577466795)
                    ·
                      rfl

theorem cell23_4327024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_4327024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327024 prefixEnd_4327024 := by exact prefixLift 4327024
  have htrace : WordTrace (prefixWord ++ tailWord_4327024) baseStart_4327024 baseEnd_4327024 := by
    simpa [prefixWord, tailWord_4327024, baseEnd_4327024] using wordTrace_append hprefix tailTrace_4327024
  have hstable : (prefixWord ++ tailWord_4327024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327024).length < 2 ^ (prefixWord ++ tailWord_4327024).sum := by decide
  have hdescent : baseEnd_4327024 < baseStart_4327024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327037 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 6]
def baseStart_4327037 : Nat := 118140960795 + 4327037 * 2 ^ 59
def prefixEnd_4327037 : Nat := 4983230072969 + 3 ^ 40 * 4327037 * 2
def baseEnd_4327037 : Nat := 246872198976543575726425

theorem tailTrace_4327037 : CollatzResearch.WordTrace tailWord_4327037 prefixEnd_4327037 246872198976543575726425 := by
  unfold tailWord_4327037
  simp only [CollatzResearch.WordTrace]
  refine ⟨157820004824891422929987365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105213336549927615286658243 157820004824891422929987365)
  ·
    refine ⟨29591250904667141799372631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157820004824891422929987365 29591250904667141799372631)
    ·
      refine ⟨44386876357000712699058947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29591250904667141799372631 44386876357000712699058947)
      ·
        refine ⟨66580314535501069048588421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44386876357000712699058947 66580314535501069048588421)
        ·
          refine ⟨12483808975406450446610329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66580314535501069048588421 12483808975406450446610329)
          ·
            refine ⟨9362856731554837834957747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12483808975406450446610329 9362856731554837834957747)
            ·
              refine ⟨14044285097332256752436621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9362856731554837834957747 14044285097332256752436621)
              ·
                refine ⟨5266606911499596282163733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14044285097332256752436621 5266606911499596282163733)
                ·
                  refine ⟨246872198976543575726425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5266606911499596282163733 246872198976543575726425)
                  ·
                    rfl

theorem cell23_4327037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_4327037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327037 prefixEnd_4327037 := by exact prefixLift 4327037
  have htrace : WordTrace (prefixWord ++ tailWord_4327037) baseStart_4327037 baseEnd_4327037 := by
    simpa [prefixWord, tailWord_4327037, baseEnd_4327037] using wordTrace_append hprefix tailTrace_4327037
  have hstable : (prefixWord ++ tailWord_4327037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327037).length < 2 ^ (prefixWord ++ tailWord_4327037).sum := by decide
  have hdescent : baseEnd_4327037 < baseStart_4327037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327121 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 1, 1, 4]
def baseStart_4327121 : Nat := 118140960795 + 4327121 * 2 ^ 59
def prefixEnd_4327121 : Nat := 4983230072969 + 3 ^ 40 * 4327121 * 2
def baseEnd_4327121 : Nat := 2221892923163869852887439

theorem tailTrace_4327121 : CollatzResearch.WordTrace tailWord_4327121 prefixEnd_4327121 2221892923163869852887439 := by
  unfold tailWord_4327121
  simp only [CollatzResearch.WordTrace]
  refine ⟨157823068556587105276045217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105215379037724736850696811 157823068556587105276045217)
  ·
    refine ⟨118367301417440328957033913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157823068556587105276045217 118367301417440328957033913)
    ·
      refine ⟨88775476063080246717775435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118367301417440328957033913 88775476063080246717775435)
      ·
        refine ⟨133163214094620370076663153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88775476063080246717775435 133163214094620370076663153)
        ·
          refine ⟨99872410570965277557497365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133163214094620370076663153 99872410570965277557497365)
          ·
            refine ⟨4681519245513997385507689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99872410570965277557497365 4681519245513997385507689)
            ·
              refine ⟨3511139434135498039130767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4681519245513997385507689 3511139434135498039130767)
              ·
                refine ⟨5266709151203247058696151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511139434135498039130767 5266709151203247058696151)
                ·
                  refine ⟨7900063726804870588044227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5266709151203247058696151 7900063726804870588044227)
                  ·
                    refine ⟨11850095590207305882066341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7900063726804870588044227 11850095590207305882066341)
                    ·
                      refine ⟨2221892923163869852887439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11850095590207305882066341 2221892923163869852887439)
                      ·
                        rfl

theorem cell23_4327121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_4327121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327121 prefixEnd_4327121 := by exact prefixLift 4327121
  have htrace : WordTrace (prefixWord ++ tailWord_4327121) baseStart_4327121 baseEnd_4327121 := by
    simpa [prefixWord, tailWord_4327121, baseEnd_4327121] using wordTrace_append hprefix tailTrace_4327121
  have hstable : (prefixWord ++ tailWord_4327121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327121).length < 2 ^ (prefixWord ++ tailWord_4327121).sum := by decide
  have hdescent : baseEnd_4327121 < baseStart_4327121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327160 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_4327160 : Nat := 118140960795 + 4327160 * 2 ^ 59
def prefixEnd_4327160 : Nat := 4983230072969 + 3 ^ 40 * 4327160 * 2
def baseEnd_4327160 : Nat := 2221912948909395200299759

theorem tailTrace_4327160 : CollatzResearch.WordTrace tailWord_4327160 prefixEnd_4327160 2221912948909395200299759 := by
  unfold tailWord_4327160
  simp only [CollatzResearch.WordTrace]
  refine ⟨78912245501722907468357467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105216327335630543291143289 78912245501722907468357467)
  ·
    refine ⟨118368368252584361202536201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78912245501722907468357467 118368368252584361202536201)
    ·
      refine ⟨88776276189438270901902151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118368368252584361202536201 88776276189438270901902151)
      ·
        refine ⟨133164414284157406352853227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88776276189438270901902151 133164414284157406352853227)
        ·
          refine ⟨199746621426236109529279841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133164414284157406352853227 199746621426236109529279841)
          ·
            refine ⟨149809966069677082146959881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199746621426236109529279841 149809966069677082146959881)
            ·
              refine ⟨112357474552257811610219911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149809966069677082146959881 112357474552257811610219911)
              ·
                refine ⟨168536211828386717415329867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112357474552257811610219911 168536211828386717415329867)
                ·
                  refine ⟨252804317742580076122994801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168536211828386717415329867 252804317742580076122994801)
                  ·
                    refine ⟨189603238306935057092246101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 252804317742580076122994801 189603238306935057092246101)
                    ·
                      refine ⟨2221912948909395200299759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189603238306935057092246101 2221912948909395200299759)
                      ·
                        rfl

theorem cell23_4327160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_4327160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327160 prefixEnd_4327160 := by exact prefixLift 4327160
  have htrace : WordTrace (prefixWord ++ tailWord_4327160) baseStart_4327160 baseEnd_4327160 := by
    simpa [prefixWord, tailWord_4327160, baseEnd_4327160] using wordTrace_append hprefix tailTrace_4327160
  have hstable : (prefixWord ++ tailWord_4327160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327160).length < 2 ^ (prefixWord ++ tailWord_4327160).sum := by decide
  have hdescent : baseEnd_4327160 < baseStart_4327160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327245 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4327245 : Nat := 118140960795 + 4327245 * 2 ^ 59
def prefixEnd_4327245 : Nat := 4983230072969 + 3 ^ 40 * 4327245 * 2
def baseEnd_4327245 : Nat := 2221956594765027367736869

theorem tailTrace_4327245 : CollatzResearch.WordTrace tailWord_4327245 prefixEnd_4327245 2221956594765027367736869 := by
  unfold tailWord_4327245
  simp only [CollatzResearch.WordTrace]
  refine ⟨157827591208137874453559189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105218394138758582969039459 157827591208137874453559189)
  ·
    refine ⟨7398168337881462865010587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 157827591208137874453559189 7398168337881462865010587)
    ·
      refine ⟨11097252506822194297515881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7398168337881462865010587 11097252506822194297515881)
      ·
        refine ⟨8322939380116645723136911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11097252506822194297515881 8322939380116645723136911)
        ·
          refine ⟨12484409070174968584705367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8322939380116645723136911 12484409070174968584705367)
          ·
            refine ⟨18726613605262452877058051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12484409070174968584705367 18726613605262452877058051)
            ·
              refine ⟨28089920407893679315587077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18726613605262452877058051 28089920407893679315587077)
              ·
                refine ⟨5266860076480064871672577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28089920407893679315587077 5266860076480064871672577)
                ·
                  refine ⟨3950145057360048653754433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5266860076480064871672577 3950145057360048653754433)
                  ·
                    refine ⟨2962608793020036490315825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950145057360048653754433 2962608793020036490315825)
                    ·
                      refine ⟨2221956594765027367736869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962608793020036490315825 2221956594765027367736869)
                      ·
                        rfl

theorem cell23_4327245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4327245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327245 prefixEnd_4327245 := by exact prefixLift 4327245
  have htrace : WordTrace (prefixWord ++ tailWord_4327245) baseStart_4327245 baseEnd_4327245 := by
    simpa [prefixWord, tailWord_4327245, baseEnd_4327245] using wordTrace_append hprefix tailTrace_4327245
  have hstable : (prefixWord ++ tailWord_4327245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327245).length < 2 ^ (prefixWord ++ tailWord_4327245).sum := by decide
  have hdescent : baseEnd_4327245 < baseStart_4327245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327257 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_4327257 : Nat := 118140960795 + 4327257 * 2 ^ 59
def prefixEnd_4327257 : Nat := 4983230072969 + 3 ^ 40 * 4327257 * 2
def baseEnd_4327257 : Nat := 2221962756532881320786813

theorem tailTrace_4327257 : CollatzResearch.WordTrace tailWord_4327257 prefixEnd_4327257 2221962756532881320786813 := by
  unfold tailWord_4327257
  simp only [CollatzResearch.WordTrace]
  refine ⟨157828028884094400502996025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105218685922729600335330683 157828028884094400502996025)
  ·
    refine ⟨118371021663070800377247019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157828028884094400502996025 118371021663070800377247019)
    ·
      refine ⟨177556532494606200565870529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118371021663070800377247019 177556532494606200565870529)
      ·
        refine ⟨133167399370954650424402897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177556532494606200565870529 133167399370954650424402897)
        ·
          refine ⟨99875549528215987818302173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133167399370954650424402897 99875549528215987818302173)
          ·
            refine ⟨37453331073080995431863315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99875549528215987818302173 37453331073080995431863315)
            ·
              refine ⟨56179996609621493147794973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37453331073080995431863315 56179996609621493147794973)
              ·
                refine ⟨21067498728608059930423115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56179996609621493147794973 21067498728608059930423115)
                ·
                  refine ⟨31601248092912089895634673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21067498728608059930423115 31601248092912089895634673)
                  ·
                    refine ⟨23700936069684067421726005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31601248092912089895634673 23700936069684067421726005)
                    ·
                      refine ⟨2221962756532881320786813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23700936069684067421726005 2221962756532881320786813)
                      ·
                        rfl

theorem cell23_4327257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_4327257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327257 prefixEnd_4327257 := by exact prefixLift 4327257
  have htrace : WordTrace (prefixWord ++ tailWord_4327257) baseStart_4327257 baseEnd_4327257 := by
    simpa [prefixWord, tailWord_4327257, baseEnd_4327257] using wordTrace_append hprefix tailTrace_4327257
  have hstable : (prefixWord ++ tailWord_4327257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327257).length < 2 ^ (prefixWord ++ tailWord_4327257).sum := by decide
  have hdescent : baseEnd_4327257 < baseStart_4327257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327345 : List Nat := [1, 2, 2, 4, 2, 3, 1, 3, 1, 4]
def baseStart_4327345 : Nat := 118140960795 + 4327345 * 2 ^ 59
def prefixEnd_4327345 : Nat := 4983230072969 + 3 ^ 40 * 4327345 * 2
def baseEnd_4327345 : Nat := 740669314276825658828803

theorem tailTrace_4327345 : CollatzResearch.WordTrace tailWord_4327345 prefixEnd_4327345 740669314276825658828803 := by
  unfold tailWord_4327345
  simp only [CollatzResearch.WordTrace]
  refine ⟨157831238507775591532199489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105220825671850394354799659 157831238507775591532199489)
  ·
    refine ⟨118373428880831693649149617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157831238507775591532199489 118373428880831693649149617)
    ·
      refine ⟨88780071660623770236862213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118373428880831693649149617 88780071660623770236862213)
      ·
        refine ⟨16646263436366956919411665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88780071660623770236862213 16646263436366956919411665)
        ·
          refine ⟨12484697577275217689558749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16646263436366956919411665 12484697577275217689558749)
          ·
            refine ⟨4681761591478206633584531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12484697577275217689558749 4681761591478206633584531)
            ·
              refine ⟨7022642387217309950376797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681761591478206633584531 7022642387217309950376797)
              ·
                refine ⟨2633490895206491231391299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7022642387217309950376797 2633490895206491231391299)
                ·
                  refine ⟨3950236342809736847086949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633490895206491231391299 3950236342809736847086949)
                  ·
                    refine ⟨740669314276825658828803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3950236342809736847086949 740669314276825658828803)
                    ·
                      rfl

theorem cell23_4327345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_4327345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327345 prefixEnd_4327345 := by exact prefixLift 4327345
  have htrace : WordTrace (prefixWord ++ tailWord_4327345) baseStart_4327345 baseEnd_4327345 := by
    simpa [prefixWord, tailWord_4327345, baseEnd_4327345] using wordTrace_append hprefix tailTrace_4327345
  have hstable : (prefixWord ++ tailWord_4327345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327345).length < 2 ^ (prefixWord ++ tailWord_4327345).sum := by decide
  have hdescent : baseEnd_4327345 < baseStart_4327345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327368 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_4327368 : Nat := 118140960795 + 4327368 * 2 ^ 59
def prefixEnd_4327368 : Nat := 4983230072969 + 3 ^ 40 * 4327368 * 2
def baseEnd_4327368 : Nat := 2222019752885530386498803

theorem tailTrace_4327368 : CollatzResearch.WordTrace tailWord_4327368 prefixEnd_4327368 2222019752885530386498803 := by
  unfold tailWord_4327368
  simp only [CollatzResearch.WordTrace]
  refine ⟨78916038693346133230143379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105221384924461510973524505 78916038693346133230143379)
  ·
    refine ⟨118374058040019199845215069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78916038693346133230143379 118374058040019199845215069)
    ·
      refine ⟨44390271765007199941955651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118374058040019199845215069 44390271765007199941955651)
      ·
        refine ⟨66585407647510799912933477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44390271765007199941955651 66585407647510799912933477)
        ·
          refine ⟨12484763933908274983675027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66585407647510799912933477 12484763933908274983675027)
          ·
            refine ⟨18727145900862412475512541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12484763933908274983675027 18727145900862412475512541)
            ·
              refine ⟨7022679712823404678317203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18727145900862412475512541 7022679712823404678317203)
              ·
                refine ⟨10534019569235107017475805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7022679712823404678317203 10534019569235107017475805)
                ·
                  refine ⟨3950257338463165131553427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10534019569235107017475805 3950257338463165131553427)
                  ·
                    refine ⟨5925386007694747697330141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950257338463165131553427 5925386007694747697330141)
                    ·
                      refine ⟨2222019752885530386498803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925386007694747697330141 2222019752885530386498803)
                      ·
                        rfl

theorem cell23_4327368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_4327368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327368 prefixEnd_4327368 := by exact prefixLift 4327368
  have htrace : WordTrace (prefixWord ++ tailWord_4327368) baseStart_4327368 baseEnd_4327368 := by
    simpa [prefixWord, tailWord_4327368, baseEnd_4327368] using wordTrace_append hprefix tailTrace_4327368
  have hstable : (prefixWord ++ tailWord_4327368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327368).length < 2 ^ (prefixWord ++ tailWord_4327368).sum := by decide
  have hdescent : baseEnd_4327368 < baseStart_4327368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327384 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_4327384 : Nat := 118140960795 + 4327384 * 2 ^ 59
def prefixEnd_4327384 : Nat := 4983230072969 + 3 ^ 40 * 4327384 * 2
def baseEnd_4327384 : Nat := 740675989525334107966243

theorem tailTrace_4327384 : CollatzResearch.WordTrace tailWord_4327384 prefixEnd_4327384 740675989525334107966243 := by
  unfold tailWord_4327384
  simp only [CollatzResearch.WordTrace]
  refine ⟨78916330477317150596434603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105221773969756200795246137 78916330477317150596434603)
  ·
    refine ⟨118374495715975725894651905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78916330477317150596434603 118374495715975725894651905)
    ·
      refine ⟨88780871786981794420988929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118374495715975725894651905 88780871786981794420988929)
      ·
        refine ⟨66585653840236345815741697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88780871786981794420988929 66585653840236345815741697)
        ·
          refine ⟨49939240380177259361806273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66585653840236345815741697 49939240380177259361806273)
          ·
            refine ⟨37454430285132944521354705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49939240380177259361806273 37454430285132944521354705)
            ·
              refine ⟨28090822713849708391016029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37454430285132944521354705 28090822713849708391016029)
              ·
                refine ⟨10534058517693640646631011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28090822713849708391016029 10534058517693640646631011)
                ·
                  refine ⟨15801087776540460969946517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10534058517693640646631011 15801087776540460969946517)
                  ·
                    refine ⟨740675989525334107966243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15801087776540460969946517 740675989525334107966243)
                    ·
                      rfl

theorem cell23_4327384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_4327384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327384 prefixEnd_4327384 := by exact prefixLift 4327384
  have htrace : WordTrace (prefixWord ++ tailWord_4327384) baseStart_4327384 baseEnd_4327384 := by
    simpa [prefixWord, tailWord_4327384, baseEnd_4327384] using wordTrace_append hprefix tailTrace_4327384
  have hstable : (prefixWord ++ tailWord_4327384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327384).length < 2 ^ (prefixWord ++ tailWord_4327384).sum := by decide
  have hdescent : baseEnd_4327384 < baseStart_4327384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327391 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_4327391 : Nat := 118140960795 + 4327391 * 2 ^ 59
def prefixEnd_4327391 : Nat := 4983230072969 + 3 ^ 40 * 4327391 * 2
def baseEnd_4327391 : Nat := 2222031562940583796511197

theorem tailTrace_4327391 : CollatzResearch.WordTrace tailWord_4327391 prefixEnd_4327391 2222031562940583796511197 := by
  unfold tailWord_4327391
  simp only [CollatzResearch.WordTrace]
  refine ⟨157832916265608941388374027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105221944177072627592249351 157832916265608941388374027)
  ·
    refine ⟨236749374398413412082561041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157832916265608941388374027 236749374398413412082561041)
    ·
      refine ⟨177562030798810059061920781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236749374398413412082561041 177562030798810059061920781)
      ·
        refine ⟨66585761549553772148220293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177562030798810059061920781 66585761549553772148220293)
        ·
          refine ⟨12484830290541332277791305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66585761549553772148220293 12484830290541332277791305)
          ·
            refine ⟨9363622717905999208343479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12484830290541332277791305 9363622717905999208343479)
            ·
              refine ⟨14045434076858998812515219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9363622717905999208343479 14045434076858998812515219)
              ·
                refine ⟨21068151115288498218772829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14045434076858998812515219 21068151115288498218772829)
                ·
                  refine ⟨7900556668233186832039811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21068151115288498218772829 7900556668233186832039811)
                  ·
                    refine ⟨11850835002349780248059717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7900556668233186832039811 11850835002349780248059717)
                    ·
                      refine ⟨2222031562940583796511197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11850835002349780248059717 2222031562940583796511197)
                      ·
                        rfl

theorem cell23_4327391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_4327391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327391 prefixEnd_4327391 := by exact prefixLift 4327391
  have htrace : WordTrace (prefixWord ++ tailWord_4327391) baseStart_4327391 baseEnd_4327391 := by
    simpa [prefixWord, tailWord_4327391, baseEnd_4327391] using wordTrace_append hprefix tailTrace_4327391
  have hstable : (prefixWord ++ tailWord_4327391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327391).length < 2 ^ (prefixWord ++ tailWord_4327391).sum := by decide
  have hdescent : baseEnd_4327391 < baseStart_4327391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327411 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 3]
def baseStart_4327411 : Nat := 118140960795 + 4327411 * 2 ^ 59
def prefixEnd_4327411 : Nat := 4983230072969 + 3 ^ 40 * 4327411 * 2
def baseEnd_4327411 : Nat := 2222041832553673718261105

theorem tailTrace_4327411 : CollatzResearch.WordTrace tailWord_4327411 prefixEnd_4327411 2222041832553673718261105 := by
  unfold tailWord_4327411
  simp only [CollatzResearch.WordTrace]
  refine ⟨157833645725536484804102087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105222430483690989869401391 157833645725536484804102087)
  ·
    refine ⟨236750468588304727206153131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157833645725536484804102087 236750468588304727206153131)
    ·
      refine ⟨355125702882457090809229697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236750468588304727206153131 355125702882457090809229697)
      ·
        refine ⟨266344277161842818106922273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355125702882457090809229697 266344277161842818106922273)
        ·
          refine ⟨199758207871382113580191705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266344277161842818106922273 199758207871382113580191705)
          ·
            refine ⟨149818655903536585185143779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199758207871382113580191705 149818655903536585185143779)
            ·
              refine ⟨224727983855304877777715669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149818655903536585185143779 224727983855304877777715669)
              ·
                refine ⟨5267062121608708072915211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 224727983855304877777715669 5267062121608708072915211)
                ·
                  refine ⟨7900593182413062109372817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5267062121608708072915211 7900593182413062109372817)
                  ·
                    refine ⟨5925444886809796582029613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7900593182413062109372817 5925444886809796582029613)
                    ·
                      refine ⟨2222041832553673718261105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925444886809796582029613 2222041832553673718261105)
                      ·
                        rfl

theorem cell23_4327411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_4327411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327411 prefixEnd_4327411 := by exact prefixLift 4327411
  have htrace : WordTrace (prefixWord ++ tailWord_4327411) baseStart_4327411 baseEnd_4327411 := by
    simpa [prefixWord, tailWord_4327411, baseEnd_4327411] using wordTrace_append hprefix tailTrace_4327411
  have hstable : (prefixWord ++ tailWord_4327411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327411).length < 2 ^ (prefixWord ++ tailWord_4327411).sum := by decide
  have hdescent : baseEnd_4327411 < baseStart_4327411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327414 : List Nat := [5, 1, 1, 1, 15]
def baseStart_4327414 : Nat := 118140960795 + 4327414 * 2 ^ 59
def prefixEnd_4327414 : Nat := 4983230072969 + 3 ^ 40 * 4327414 * 2
def baseEnd_4327414 : Nat := 3048070470501559954079

theorem tailTrace_4327414 : CollatzResearch.WordTrace tailWord_4327414 prefixEnd_4327414 3048070470501559954079 := by
  unfold tailWord_4327414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9864609696532851019778831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105222503429683744210974197 9864609696532851019778831)
  ·
    refine ⟨14796914544799276529668247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9864609696532851019778831 14796914544799276529668247)
    ·
      refine ⟨22195371817198914794502371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14796914544799276529668247 22195371817198914794502371)
      ·
        refine ⟨33293057725798372191753557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22195371817198914794502371 33293057725798372191753557)
        ·
          refine ⟨3048070470501559954079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 33293057725798372191753557 3048070470501559954079)
          ·
            rfl

theorem cell23_4327414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 15].length) (baseStart_4327414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327414 prefixEnd_4327414 := by exact prefixLift 4327414
  have htrace : WordTrace (prefixWord ++ tailWord_4327414) baseStart_4327414 baseEnd_4327414 := by
    simpa [prefixWord, tailWord_4327414, baseEnd_4327414] using wordTrace_append hprefix tailTrace_4327414
  have hstable : (prefixWord ++ tailWord_4327414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327414).length < 2 ^ (prefixWord ++ tailWord_4327414).sum := by decide
  have hdescent : baseEnd_4327414 < baseStart_4327414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327431 : List Nat := [1, 1, 4, 3, 1, 4, 1, 8]
def baseStart_4327431 : Nat := 118140960795 + 4327431 * 2 ^ 59
def prefixEnd_4327431 : Nat := 4983230072969 + 3 ^ 40 * 4327431 * 2
def baseEnd_4327431 : Nat := 82298226006176431111519

theorem tailTrace_4327431 : CollatzResearch.WordTrace tailWord_4327431 prefixEnd_4327431 82298226006176431111519 := by
  unfold tailWord_4327431
  simp only [CollatzResearch.WordTrace]
  refine ⟨157834375185464028219830147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105222916790309352146553431 157834375185464028219830147)
  ·
    refine ⟨236751562778196042329745221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157834375185464028219830147 236751562778196042329745221)
    ·
      refine ⟨44390918020911757936827229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236751562778196042329745221 44390918020911757936827229)
      ·
        refine ⟨16646594257841909226310211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44390918020911757936827229 16646594257841909226310211)
        ·
          refine ⟨24969891386762863839465317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16646594257841909226310211 24969891386762863839465317)
          ·
            refine ⟨4681854635018036969899747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24969891386762863839465317 4681854635018036969899747)
            ·
              refine ⟨7022781952527055454849621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681854635018036969899747 7022781952527055454849621)
              ·
                refine ⟨82298226006176431111519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7022781952527055454849621 82298226006176431111519)
                ·
                  rfl

theorem cell23_4327431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 8].length) (baseStart_4327431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327431 prefixEnd_4327431 := by exact prefixLift 4327431
  have htrace : WordTrace (prefixWord ++ tailWord_4327431) baseStart_4327431 baseEnd_4327431 := by
    simpa [prefixWord, tailWord_4327431, baseEnd_4327431] using wordTrace_append hprefix tailTrace_4327431
  have hstable : (prefixWord ++ tailWord_4327431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327431).length < 2 ^ (prefixWord ++ tailWord_4327431).sum := by decide
  have hdescent : baseEnd_4327431 < baseStart_4327431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327441 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_4327441 : Nat := 118140960795 + 4327441 * 2 ^ 59
def prefixEnd_4327441 : Nat := 4983230072969 + 3 ^ 40 * 4327441 * 2
def baseEnd_4327441 : Nat := 2222057236973308600885967

theorem tailTrace_4327441 : CollatzResearch.WordTrace tailWord_4327441 prefixEnd_4327441 2222057236973308600885967 := by
  unfold tailWord_4327441
  simp only [CollatzResearch.WordTrace]
  refine ⟨157834739915427799927694177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105223159943618533285129451 157834739915427799927694177)
  ·
    refine ⟨118376054936570849945770633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157834739915427799927694177 118376054936570849945770633)
    ·
      refine ⟨88782041202428137459327975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118376054936570849945770633 88782041202428137459327975)
      ·
        refine ⟨133173061803642206188991963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88782041202428137459327975 133173061803642206188991963)
        ·
          refine ⟨199759592705463309283487945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133173061803642206188991963 199759592705463309283487945)
          ·
            refine ⟨149819694529097481962615959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199759592705463309283487945 149819694529097481962615959)
            ·
              refine ⟨224729541793646222943923939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149819694529097481962615959 224729541793646222943923939)
              ·
                refine ⟨337094312690469334415885909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224729541793646222943923939 337094312690469334415885909)
                ·
                  refine ⟨3950323976841437512686163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 337094312690469334415885909 3950323976841437512686163)
                  ·
                    refine ⟨5925485965262156269029245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950323976841437512686163 5925485965262156269029245)
                    ·
                      refine ⟨2222057236973308600885967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925485965262156269029245 2222057236973308600885967)
                      ·
                        rfl

theorem cell23_4327441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_4327441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327441 prefixEnd_4327441 := by exact prefixLift 4327441
  have htrace : WordTrace (prefixWord ++ tailWord_4327441) baseStart_4327441 baseEnd_4327441 := by
    simpa [prefixWord, tailWord_4327441, baseEnd_4327441] using wordTrace_append hprefix tailTrace_4327441
  have hstable : (prefixWord ++ tailWord_4327441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327441).length < 2 ^ (prefixWord ++ tailWord_4327441).sum := by decide
  have hdescent : baseEnd_4327441 < baseStart_4327441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327458 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_4327458 : Nat := 118140960795 + 4327458 * 2 ^ 59
def prefixEnd_4327458 : Nat := 4983230072969 + 3 ^ 40 * 4327458 * 2
def baseEnd_4327458 : Nat := 2222065966144435034373389

theorem tailTrace_4327458 : CollatzResearch.WordTrace tailWord_4327458 prefixEnd_4327458 2222065966144435034373389 := by
  unfold tailWord_4327458
  simp only [CollatzResearch.WordTrace]
  refine ⟨39458839989091552957765757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105223573304244141220708685 39458839989091552957765757)
  ·
    refine ⟨14797064995909332359162159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39458839989091552957765757 14797064995909332359162159)
    ·
      refine ⟨22195597493863998538743239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14797064995909332359162159 22195597493863998538743239)
      ·
        refine ⟨33293396240795997808114859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22195597493863998538743239 33293396240795997808114859)
        ·
          refine ⟨49940094361193996712172289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33293396240795997808114859 49940094361193996712172289)
          ·
            refine ⟨37455070770895497534129217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49940094361193996712172289 37455070770895497534129217)
            ·
              refine ⟨28091303078171623150596913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37455070770895497534129217 28091303078171623150596913)
              ·
                refine ⟨21068477308628717362947685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28091303078171623150596913 21068477308628717362947685)
                ·
                  refine ⟨3950339495367884505552691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21068477308628717362947685 3950339495367884505552691)
                  ·
                    refine ⟨5925509243051826758329037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950339495367884505552691 5925509243051826758329037)
                    ·
                      refine ⟨2222065966144435034373389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925509243051826758329037 2222065966144435034373389)
                      ·
                        rfl

theorem cell23_4327458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_4327458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327458 prefixEnd_4327458 := by exact prefixLift 4327458
  have htrace : WordTrace (prefixWord ++ tailWord_4327458) baseStart_4327458 baseEnd_4327458 := by
    simpa [prefixWord, tailWord_4327458, baseEnd_4327458] using wordTrace_append hprefix tailTrace_4327458
  have hstable : (prefixWord ++ tailWord_4327458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327458).length < 2 ^ (prefixWord ++ tailWord_4327458).sum := by decide
  have hdescent : baseEnd_4327458 < baseStart_4327458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327538 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_4327538 : Nat := 118140960795 + 4327538 * 2 ^ 59
def prefixEnd_4327538 : Nat := 4983230072969 + 3 ^ 40 * 4327538 * 2
def baseEnd_4327538 : Nat := 246900782732977191263669

theorem tailTrace_4327538 : CollatzResearch.WordTrace tailWord_4327538 prefixEnd_4327538 246900782732977191263669 := by
  unfold tailWord_4327538
  simp only [CollatzResearch.WordTrace]
  refine ⟨39459569449019096373493817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105225518530717590329316845 39459569449019096373493817)
  ·
    refine ⟨29594677086764322280120363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39459569449019096373493817 29594677086764322280120363)
    ·
      refine ⟨44392015630146483420180545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29594677086764322280120363 44392015630146483420180545)
      ·
        refine ⟨33294011722609862565135409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44392015630146483420180545 33294011722609862565135409)
        ·
          refine ⟨24970508791957396923851557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33294011722609862565135409 24970508791957396923851557)
          ·
            refine ⟨4681970398492011923222167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24970508791957396923851557 4681970398492011923222167)
            ·
              refine ⟨7022955597738017884833251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4681970398492011923222167 7022955597738017884833251)
              ·
                refine ⟨10534433396607026827249877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7022955597738017884833251 10534433396607026827249877)
                ·
                  refine ⟨246900782732977191263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10534433396607026827249877 246900782732977191263669)
                  ·
                    rfl

theorem cell23_4327538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_4327538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327538 prefixEnd_4327538 := by exact prefixLift 4327538
  have htrace : WordTrace (prefixWord ++ tailWord_4327538) baseStart_4327538 baseEnd_4327538 := by
    simpa [prefixWord, tailWord_4327538, baseEnd_4327538] using wordTrace_append hprefix tailTrace_4327538
  have hstable : (prefixWord ++ tailWord_4327538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327538).length < 2 ^ (prefixWord ++ tailWord_4327538).sum := by decide
  have hdescent : baseEnd_4327538 < baseStart_4327538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327549 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_4327549 : Nat := 118140960795 + 4327549 * 2 ^ 59
def prefixEnd_4327549 : Nat := 4983230072969 + 3 ^ 40 * 4327549 * 2
def baseEnd_4327549 : Nat := 2222112692883994178335471

theorem tailTrace_4327549 : CollatzResearch.WordTrace tailWord_4327549 prefixEnd_4327549 2222112692883994178335471 := by
  unfold tailWord_4327549
  simp only [CollatzResearch.WordTrace]
  refine ⟨157838678999036534372625701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105225785999357689581750467 157838678999036534372625701)
  ·
    refine ⟨29594752312319350194867319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157838678999036534372625701 29594752312319350194867319)
    ·
      refine ⟨44392128468479025292300979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29594752312319350194867319 44392128468479025292300979)
      ·
        refine ⟨66588192702718537938451469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44392128468479025292300979 66588192702718537938451469)
        ·
          refine ⟨24970572263519451726919301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66588192702718537938451469 24970572263519451726919301)
          ·
            refine ⟨4681982299409897198797369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24970572263519451726919301 4681982299409897198797369)
            ·
              refine ⟨3511486724557422899098027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4681982299409897198797369 3511486724557422899098027)
              ·
                refine ⟨5267230086836134348647041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3511486724557422899098027 5267230086836134348647041)
                ·
                  refine ⟨3950422565127100761485281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267230086836134348647041 3950422565127100761485281)
                  ·
                    refine ⟨2962816923845325571113961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950422565127100761485281 2962816923845325571113961)
                    ·
                      refine ⟨2222112692883994178335471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962816923845325571113961 2222112692883994178335471)
                      ·
                        rfl

theorem cell23_4327549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_4327549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327549 prefixEnd_4327549 := by exact prefixLift 4327549
  have htrace : WordTrace (prefixWord ++ tailWord_4327549) baseStart_4327549 baseEnd_4327549 := by
    simpa [prefixWord, tailWord_4327549, baseEnd_4327549] using wordTrace_append hprefix tailTrace_4327549
  have hstable : (prefixWord ++ tailWord_4327549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327549).length < 2 ^ (prefixWord ++ tailWord_4327549).sum := by decide
  have hdescent : baseEnd_4327549 < baseStart_4327549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327611 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 6]
def baseStart_4327611 : Nat := 118140960795 + 4327611 * 2 ^ 59
def prefixEnd_4327611 : Nat := 4983230072969 + 3 ^ 40 * 4327611 * 2
def baseEnd_4327611 : Nat := 246904947631619215084465

theorem tailTrace_4327611 : CollatzResearch.WordTrace tailWord_4327611 prefixEnd_4327611 246904947631619215084465 := by
  unfold tailWord_4327611
  simp only [CollatzResearch.WordTrace]
  refine ⟨157840940324811918961382687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105227293549874612640921791 157840940324811918961382687)
  ·
    refine ⟨236761410487217878442074031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157840940324811918961382687 236761410487217878442074031)
    ·
      refine ⟨355142115730826817663111047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236761410487217878442074031 355142115730826817663111047)
      ·
        refine ⟨532713173596240226494666571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355142115730826817663111047 532713173596240226494666571)
        ·
          refine ⟨799069760394360339741999857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532713173596240226494666571 799069760394360339741999857)
          ·
            refine ⟨599302320295770254806499893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799069760394360339741999857 599302320295770254806499893)
            ·
              refine ⟨56184592527728461388109365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 599302320295770254806499893 56184592527728461388109365)
              ·
                refine ⟨5267305549474543255135253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56184592527728461388109365 5267305549474543255135253)
                ·
                  refine ⟨246904947631619215084465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5267305549474543255135253 246904947631619215084465)
                  ·
                    rfl

theorem cell23_4327611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 6].length) (baseStart_4327611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327611 prefixEnd_4327611 := by exact prefixLift 4327611
  have htrace : WordTrace (prefixWord ++ tailWord_4327611) baseStart_4327611 baseEnd_4327611 := by
    simpa [prefixWord, tailWord_4327611, baseEnd_4327611] using wordTrace_append hprefix tailTrace_4327611
  have hstable : (prefixWord ++ tailWord_4327611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327611).length < 2 ^ (prefixWord ++ tailWord_4327611).sum := by decide
  have hdescent : baseEnd_4327611 < baseStart_4327611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327645 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 6]
def baseStart_4327645 : Nat := 118140960795 + 4327645 * 2 ^ 59
def prefixEnd_4327645 : Nat := 4983230072969 + 3 ^ 40 * 4327645 * 2
def baseEnd_4327645 : Nat := 246906887447425089192781

theorem tailTrace_4327645 : CollatzResearch.WordTrace tailWord_4327645 prefixEnd_4327645 246906887447425089192781 := by
  unfold tailWord_4327645
  simp only [CollatzResearch.WordTrace]
  refine ⟨157842180406688742768120389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105228120271125828512080259 157842180406688742768120389)
  ·
    refine ⟨29595408826254139269022573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157842180406688742768120389 29595408826254139269022573)
    ·
      refine ⟨11098278309845302225883465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29595408826254139269022573 11098278309845302225883465)
      ·
        refine ⟨8323708732383976669412599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11098278309845302225883465 8323708732383976669412599)
        ·
          refine ⟨12485563098575965004118899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8323708732383976669412599 12485563098575965004118899)
          ·
            refine ⟨18728344647863947506178349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12485563098575965004118899 18728344647863947506178349)
            ·
              refine ⟨7023129242948980314816881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18728344647863947506178349 7023129242948980314816881)
              ·
                refine ⟨5267346932211735236112661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7023129242948980314816881 5267346932211735236112661)
                ·
                  refine ⟨246906887447425089192781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5267346932211735236112661 246906887447425089192781)
                  ·
                    rfl

theorem cell23_4327645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_4327645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327645 prefixEnd_4327645 := by exact prefixLift 4327645
  have htrace : WordTrace (prefixWord ++ tailWord_4327645) baseStart_4327645 baseEnd_4327645 := by
    simpa [prefixWord, tailWord_4327645, baseEnd_4327645] using wordTrace_append hprefix tailTrace_4327645
  have hstable : (prefixWord ++ tailWord_4327645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327645).length < 2 ^ (prefixWord ++ tailWord_4327645).sum := by decide
  have hdescent : baseEnd_4327645 < baseStart_4327645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327682 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_4327682 : Nat := 118140960795 + 4327682 * 2 ^ 59
def prefixEnd_4327682 : Nat := 4983230072969 + 3 ^ 40 * 4327682 * 2
def baseEnd_4327682 : Nat := 2222180985811042157972359

theorem tailTrace_4327682 : CollatzResearch.WordTrace tailWord_4327682 prefixEnd_4327682 2222180985811042157972359 := by
  unfold tailWord_4327682
  simp only [CollatzResearch.WordTrace]
  refine ⟨39460882476888674521804325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105229019938369798724811533 39460882476888674521804325)
  ·
    refine ⟨7398915464416626472838311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39460882476888674521804325 7398915464416626472838311)
    ·
      refine ⟨11098373196624939709257467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7398915464416626472838311 11098373196624939709257467)
      ·
        refine ⟨16647559794937409563886201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11098373196624939709257467 16647559794937409563886201)
        ·
          refine ⟨12485669846203057172914651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16647559794937409563886201 12485669846203057172914651)
          ·
            refine ⟨18728504769304585759371977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12485669846203057172914651 18728504769304585759371977)
            ·
              refine ⟨14046378576978439319528983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18728504769304585759371977 14046378576978439319528983)
              ·
                refine ⟨21069567865467658979293475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14046378576978439319528983 21069567865467658979293475)
                ·
                  refine ⟨31604351798201488468940213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21069567865467658979293475 31604351798201488468940213)
                  ·
                    refine ⟨2962907981081389543963145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31604351798201488468940213 2962907981081389543963145)
                    ·
                      refine ⟨2222180985811042157972359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962907981081389543963145 2222180985811042157972359)
                      ·
                        rfl

theorem cell23_4327682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_4327682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327682 prefixEnd_4327682 := by exact prefixLift 4327682
  have htrace : WordTrace (prefixWord ++ tailWord_4327682) baseStart_4327682 baseEnd_4327682 := by
    simpa [prefixWord, tailWord_4327682, baseEnd_4327682] using wordTrace_append hprefix tailTrace_4327682
  have hstable : (prefixWord ++ tailWord_4327682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327682).length < 2 ^ (prefixWord ++ tailWord_4327682).sum := by decide
  have hdescent : baseEnd_4327682 < baseStart_4327682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327689 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 1, 1, 3]
def baseStart_4327689 : Nat := 118140960795 + 4327689 * 2 ^ 59
def prefixEnd_4327689 : Nat := 4983230072969 + 3 ^ 40 * 4327689 * 2
def baseEnd_4327689 : Nat := 2222184580175623630584827

theorem tailTrace_4327689 : CollatzResearch.WordTrace tailWord_4327689 prefixEnd_4327689 2222184580175623630584827 := by
  unfold tailWord_4327689
  simp only [CollatzResearch.WordTrace]
  refine ⟨157843785218529338282722121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105229190145686225521814747 157843785218529338282722121)
  ·
    refine ⟨118382838913897003712041591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157843785218529338282722121 118382838913897003712041591)
    ·
      refine ⟨177574258370845505568062387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118382838913897003712041591 177574258370845505568062387)
      ·
        refine ⟨266361387556268258352093581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177574258370845505568062387 266361387556268258352093581)
        ·
          refine ⟨99885520333600596882035093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266361387556268258352093581 99885520333600596882035093)
          ·
            refine ⟨4682133765637527978845395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99885520333600596882035093 4682133765637527978845395)
            ·
              refine ⟨7023200648456291968268093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682133765637527978845395 7023200648456291968268093)
              ·
                refine ⟨2633700243171109488100535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7023200648456291968268093 2633700243171109488100535)
                ·
                  refine ⟨3950550364756664232150803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633700243171109488100535 3950550364756664232150803)
                  ·
                    refine ⟨5925825547134996348226205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950550364756664232150803 5925825547134996348226205)
                    ·
                      refine ⟨2222184580175623630584827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925825547134996348226205 2222184580175623630584827)
                      ·
                        rfl

theorem cell23_4327689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 1, 1, 3].length) (baseStart_4327689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327689 prefixEnd_4327689 := by exact prefixLift 4327689
  have htrace : WordTrace (prefixWord ++ tailWord_4327689) baseStart_4327689 baseEnd_4327689 := by
    simpa [prefixWord, tailWord_4327689, baseEnd_4327689] using wordTrace_append hprefix tailTrace_4327689
  have hstable : (prefixWord ++ tailWord_4327689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327689).length < 2 ^ (prefixWord ++ tailWord_4327689).sum := by decide
  have hdescent : baseEnd_4327689 < baseStart_4327689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327695 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 5, 2, 2]
def baseStart_4327695 : Nat := 118140960795 + 4327695 * 2 ^ 59
def prefixEnd_4327695 : Nat := 4983230072969 + 3 ^ 40 * 4327695 * 2
def baseEnd_4327695 : Nat := 2222187661059550607109799

theorem tailTrace_4327695 : CollatzResearch.WordTrace tailWord_4327695 prefixEnd_4327695 2222187661059550607109799 := by
  unfold tailWord_4327695
  simp only [CollatzResearch.WordTrace]
  refine ⟨157844004056507601307440539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105229336037671734204960359 157844004056507601307440539)
  ·
    refine ⟨236766006084761401961160809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157844004056507601307440539 236766006084761401961160809)
    ·
      refine ⟨177574504563571051470870607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236766006084761401961160809 177574504563571051470870607)
      ·
        refine ⟨266361756845356577206305911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177574504563571051470870607 266361756845356577206305911)
        ·
          refine ⟨399542635268034865809458867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266361756845356577206305911 399542635268034865809458867)
          ·
            refine ⟨599313952902052298714188301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399542635268034865809458867 599313952902052298714188301)
            ·
              refine ⟨224742732338269612017820613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599313952902052298714188301 224742732338269612017820613)
              ·
                refine ⟨42139262313425552253341365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224742732338269612017820613 42139262313425552253341365)
                ·
                  refine ⟨3950555841883645523750753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42139262313425552253341365 3950555841883645523750753)
                  ·
                    refine ⟨2962916881412734142813065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950555841883645523750753 2962916881412734142813065)
                    ·
                      refine ⟨2222187661059550607109799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2962916881412734142813065 2222187661059550607109799)
                      ·
                        rfl

theorem cell23_4327695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 2, 2].length) (baseStart_4327695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327695 prefixEnd_4327695 := by exact prefixLift 4327695
  have htrace : WordTrace (prefixWord ++ tailWord_4327695) baseStart_4327695 baseEnd_4327695 := by
    simpa [prefixWord, tailWord_4327695, baseEnd_4327695] using wordTrace_append hprefix tailTrace_4327695
  have hstable : (prefixWord ++ tailWord_4327695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327695).length < 2 ^ (prefixWord ++ tailWord_4327695).sum := by decide
  have hdescent : baseEnd_4327695 < baseStart_4327695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327701 : List Nat := [1, 3, 2, 1, 2, 1, 13]
def baseStart_4327701 : Nat := 118140960795 + 4327701 * 2 ^ 59
def prefixEnd_4327701 : Nat := 4983230072969 + 3 ^ 40 * 4327701 * 2
def baseEnd_4327701 : Nat := 27434453604240463995491

theorem tailTrace_4327701 : CollatzResearch.WordTrace tailWord_4327701 prefixEnd_4327701 27434453604240463995491 := by
  unfold tailWord_4327701
  simp only [CollatzResearch.WordTrace]
  refine ⟨157844222894485864332158957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105229481929657242888105971 157844222894485864332158957)
  ·
    refine ⟨59191583585432199124559609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157844222894485864332158957 59191583585432199124559609)
    ·
      refine ⟨44393687689074149343419707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59191583585432199124559609 44393687689074149343419707)
      ·
        refine ⟨66590531533611224015129561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44393687689074149343419707 66590531533611224015129561)
        ·
          refine ⟨49942898650208418011347171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66590531533611224015129561 49942898650208418011347171)
          ·
            refine ⟨74914347975312627017020757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49942898650208418011347171 74914347975312627017020757)
            ·
              refine ⟨27434453604240463995491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 74914347975312627017020757 27434453604240463995491)
              ·
                rfl

theorem cell23_4327701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 13].length) (baseStart_4327701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327701 prefixEnd_4327701 := by exact prefixLift 4327701
  have htrace : WordTrace (prefixWord ++ tailWord_4327701) baseStart_4327701 baseEnd_4327701 := by
    simpa [prefixWord, tailWord_4327701, baseEnd_4327701] using wordTrace_append hprefix tailTrace_4327701
  have hstable : (prefixWord ++ tailWord_4327701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327701).length < 2 ^ (prefixWord ++ tailWord_4327701).sum := by decide
  have hdescent : baseEnd_4327701 < baseStart_4327701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327706 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3]
def baseStart_4327706 : Nat := 118140960795 + 4327706 * 2 ^ 59
def prefixEnd_4327706 : Nat := 4983230072969 + 3 ^ 40 * 4327706 * 2
def baseEnd_4327706 : Nat := 2222193309346750064072249

theorem tailTrace_4327706 : CollatzResearch.WordTrace tailWord_4327706 prefixEnd_4327706 2222193309346750064072249 := by
  unfold tailWord_4327706
  simp only [CollatzResearch.WordTrace]
  refine ⟨39461101314866937546522743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105229603506311833457393981 39461101314866937546522743)
  ·
    refine ⟨59191651972300406319784115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39461101314866937546522743 59191651972300406319784115)
    ·
      refine ⟨88787477958450609479676173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59191651972300406319784115 88787477958450609479676173)
      ·
        refine ⟨33295304234418978554878565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88787477958450609479676173 33295304234418978554878565)
        ·
          refine ⟨6242869543953558479039731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33295304234418978554878565 6242869543953558479039731)
          ·
            refine ⟨9364304315930337718559597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6242869543953558479039731 9364304315930337718559597)
            ·
              refine ⟨3511614118473876644459849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9364304315930337718559597 3511614118473876644459849)
              ·
                refine ⟨2633710588855407483344887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511614118473876644459849 2633710588855407483344887)
                ·
                  refine ⟨3950565883283111225017331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633710588855407483344887 3950565883283111225017331)
                  ·
                    refine ⟨5925848824924666837525997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950565883283111225017331 5925848824924666837525997)
                    ·
                      refine ⟨2222193309346750064072249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925848824924666837525997 2222193309346750064072249)
                      ·
                        rfl

theorem cell23_4327706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_4327706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327706 prefixEnd_4327706 := by exact prefixLift 4327706
  have htrace : WordTrace (prefixWord ++ tailWord_4327706) baseStart_4327706 baseEnd_4327706 := by
    simpa [prefixWord, tailWord_4327706, baseEnd_4327706] using wordTrace_append hprefix tailTrace_4327706
  have hstable : (prefixWord ++ tailWord_4327706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327706).length < 2 ^ (prefixWord ++ tailWord_4327706).sum := by decide
  have hdescent : baseEnd_4327706 < baseStart_4327706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327726 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4327726 : Nat := 118140960795 + 4327726 * 2 ^ 59
def prefixEnd_4327726 : Nat := 4983230072969 + 3 ^ 40 * 4327726 * 2
def baseEnd_4327726 : Nat := 740734526319946661940719

theorem tailTrace_4327726 : CollatzResearch.WordTrace tailWord_4327726 prefixEnd_4327726 740734526319946661940719 := by
  unfold tailWord_4327726
  simp only [CollatzResearch.WordTrace]
  refine ⟨19730641839924411700227379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105230089812930195734546021 19730641839924411700227379)
  ·
    refine ⟨29595962759886617550341069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19730641839924411700227379 29595962759886617550341069)
    ·
      refine ⟨11098486034957481581377901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29595962759886617550341069 11098486034957481581377901)
      ·
        refine ⟨4161932263109055593016713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11098486034957481581377901 4161932263109055593016713)
        ·
          refine ⟨3121449197331791694762535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4161932263109055593016713 3121449197331791694762535)
          ·
            refine ⟨4682173795997687542143803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121449197331791694762535 4682173795997687542143803)
            ·
              refine ⟨7023260693996531313215705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682173795997687542143803 7023260693996531313215705)
              ·
                refine ⟨5267445520497398484911779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7023260693996531313215705 5267445520497398484911779)
                ·
                  refine ⟨7901168280746097727367669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5267445520497398484911779 7901168280746097727367669)
                  ·
                    refine ⟨740734526319946661940719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7901168280746097727367669 740734526319946661940719)
                    ·
                      rfl

theorem cell23_4327726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4327726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327726 prefixEnd_4327726 := by exact prefixLift 4327726
  have htrace : WordTrace (prefixWord ++ tailWord_4327726) baseStart_4327726 baseEnd_4327726 := by
    simpa [prefixWord, tailWord_4327726, baseEnd_4327726] using wordTrace_append hprefix tailTrace_4327726
  have hstable : (prefixWord ++ tailWord_4327726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327726).length < 2 ^ (prefixWord ++ tailWord_4327726).sum := by decide
  have hdescent : baseEnd_4327726 < baseStart_4327726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327729 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 1, 1, 4]
def baseStart_4327729 : Nat := 118140960795 + 4327729 * 2 ^ 59
def prefixEnd_4327729 : Nat := 4983230072969 + 3 ^ 40 * 4327729 * 2
def baseEnd_4327729 : Nat := 2222205119401803474084643

theorem tailTrace_4327729 : CollatzResearch.WordTrace tailWord_4327729 prefixEnd_4327729 2222205119401803474084643 := by
  unfold tailWord_4327729
  simp only [CollatzResearch.WordTrace]
  refine ⟨157845244138384425114178241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105230162758922950076118827 157845244138384425114178241)
  ·
    refine ⟨118383933103788318835633681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157845244138384425114178241 118383933103788318835633681)
    ·
      refine ⟨88787949827841239126725261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118383933103788318835633681 88787949827841239126725261)
      ·
        refine ⟨33295481185440464672521973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88787949827841239126725261 33295481185440464672521973)
        ·
          refine ⟨3121451361135043563048935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33295481185440464672521973 3121451361135043563048935)
          ·
            refine ⟨4682177041702565344573403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121451361135043563048935 4682177041702565344573403)
            ·
              refine ⟨7023265562553848016860105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682177041702565344573403 7023265562553848016860105)
              ·
                refine ⟨5267449171915386012645079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7023265562553848016860105 5267449171915386012645079)
                ·
                  refine ⟨7901173757873079018967619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5267449171915386012645079 7901173757873079018967619)
                  ·
                    refine ⟨11851760636809618528451429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7901173757873079018967619 11851760636809618528451429)
                    ·
                      refine ⟨2222205119401803474084643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11851760636809618528451429 2222205119401803474084643)
                      ·
                        rfl

theorem cell23_4327729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_4327729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327729 prefixEnd_4327729 := by exact prefixLift 4327729
  have htrace : WordTrace (prefixWord ++ tailWord_4327729) baseStart_4327729 baseEnd_4327729 := by
    simpa [prefixWord, tailWord_4327729, baseEnd_4327729] using wordTrace_append hprefix tailTrace_4327729
  have hstable : (prefixWord ++ tailWord_4327729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327729).length < 2 ^ (prefixWord ++ tailWord_4327729).sum := by decide
  have hdescent : baseEnd_4327729 < baseStart_4327729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327732 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_4327732 : Nat := 118140960795 + 4327732 * 2 ^ 59
def prefixEnd_4327732 : Nat := 4983230072969 + 3 ^ 40 * 4327732 * 2
def baseEnd_4327732 : Nat := 2222206659843766962347129

theorem tailTrace_4327732 : CollatzResearch.WordTrace tailWord_4327732 prefixEnd_4327732 2222206659843766962347129 := by
  unfold tailWord_4327732
  simp only [CollatzResearch.WordTrace]
  refine ⟨78922676778686778313268725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105230235704915704417691633 78922676778686778313268725)
  ·
    refine ⟨7399000948001885466868943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78922676778686778313268725 7399000948001885466868943)
    ·
      refine ⟨11098501422002828200303415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7399000948001885466868943 11098501422002828200303415)
      ·
        refine ⟨16647752133004242300455123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11098501422002828200303415 16647752133004242300455123)
        ·
          refine ⟨24971628199506363450682685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16647752133004242300455123 24971628199506363450682685)
          ·
            refine ⟨9364360574814886294006007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24971628199506363450682685 9364360574814886294006007)
            ·
              refine ⟨14046540862222329441009011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9364360574814886294006007 14046540862222329441009011)
              ·
                refine ⟨21069811293333494161513517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14046540862222329441009011 21069811293333494161513517)
                ·
                  refine ⟨7901179235000060310567569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21069811293333494161513517 7901179235000060310567569)
                  ·
                    refine ⟨5925884426250045232925677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7901179235000060310567569 5925884426250045232925677)
                    ·
                      refine ⟨2222206659843766962347129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925884426250045232925677 2222206659843766962347129)
                      ·
                        rfl

theorem cell23_4327732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_4327732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327732 prefixEnd_4327732 := by exact prefixLift 4327732
  have htrace : WordTrace (prefixWord ++ tailWord_4327732) baseStart_4327732 baseEnd_4327732 := by
    simpa [prefixWord, tailWord_4327732, baseEnd_4327732] using wordTrace_append hprefix tailTrace_4327732
  have hstable : (prefixWord ++ tailWord_4327732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327732).length < 2 ^ (prefixWord ++ tailWord_4327732).sum := by decide
  have hdescent : baseEnd_4327732 < baseStart_4327732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327762 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_4327762 : Nat := 118140960795 + 4327762 * 2 ^ 59
def prefixEnd_4327762 : Nat := 4983230072969 + 3 ^ 40 * 4327762 * 2
def baseEnd_4327762 : Nat := 2222222064263401844971991

theorem tailTrace_4327762 : CollatzResearch.WordTrace tailWord_4327762 prefixEnd_4327762 2222222064263401844971991 := by
  unfold tailWord_4327762
  simp only [CollatzResearch.WordTrace]
  refine ⟨39461611936816217937532385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105230965164843247833419693 39461611936816217937532385)
  ·
    refine ⟨29596208952612163453149289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39461611936816217937532385 29596208952612163453149289)
    ·
      refine ⟨22197156714459122589861967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29596208952612163453149289 22197156714459122589861967)
      ·
        refine ⟨33295735071688683884792951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22197156714459122589861967 33295735071688683884792951)
        ·
          refine ⟨49943602607533025827189427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33295735071688683884792951 49943602607533025827189427)
          ·
            refine ⟨74915403911299538740784141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49943602607533025827189427 74915403911299538740784141)
            ·
              refine ⟨28093276466737327027794053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74915403911299538740784141 28093276466737327027794053)
              ·
                refine ⟨5267489337513248817711385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28093276466737327027794053 5267489337513248817711385)
                ·
                  refine ⟨3950617003134936613283539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267489337513248817711385 3950617003134936613283539)
                  ·
                    refine ⟨5925925504702404919925309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3950617003134936613283539 5925925504702404919925309)
                    ·
                      refine ⟨2222222064263401844971991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5925925504702404919925309 2222222064263401844971991)
                      ·
                        rfl

theorem cell23_4327762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_4327762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327762 prefixEnd_4327762 := by exact prefixLift 4327762
  have htrace : WordTrace (prefixWord ++ tailWord_4327762) baseStart_4327762 baseEnd_4327762 := by
    simpa [prefixWord, tailWord_4327762, baseEnd_4327762] using wordTrace_append hprefix tailTrace_4327762
  have hstable : (prefixWord ++ tailWord_4327762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327762).length < 2 ^ (prefixWord ++ tailWord_4327762).sum := by decide
  have hdescent : baseEnd_4327762 < baseStart_4327762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327819 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 2, 2, 2]
def baseStart_4327819 : Nat := 118140960795 + 4327819 * 2 ^ 59
def prefixEnd_4327819 : Nat := 4983230072969 + 3 ^ 40 * 4327819 * 2
def baseEnd_4327819 : Nat := 2222251332660708121959229

theorem tailTrace_4327819 : CollatzResearch.WordTrace tailWord_4327819 prefixEnd_4327819 2222251332660708121959229 := by
  unfold tailWord_4327819
  simp only [CollatzResearch.WordTrace]
  refine ⟨157848526708058370484954511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105232351138705580323303007 157848526708058370484954511)
  ·
    refine ⟨236772790062087555727431767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157848526708058370484954511 236772790062087555727431767)
    ·
      refine ⟨355159185093131333591147651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236772790062087555727431767 355159185093131333591147651)
      ·
        refine ⟨532738777639697000386721477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355159185093131333591147651 532738777639697000386721477)
        ·
          refine ⟨99888520807443187572510277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 532738777639697000386721477 99888520807443187572510277)
          ·
            refine ⟨18729097651395597669845677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99888520807443187572510277 18729097651395597669845677)
            ·
              refine ⟨7023411619273349126192129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18729097651395597669845677 7023411619273349126192129)
              ·
                refine ⟨5267558714455011844644097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7023411619273349126192129 5267558714455011844644097)
                ·
                  refine ⟨3950669035841258883483073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5267558714455011844644097 3950669035841258883483073)
                  ·
                    refine ⟨2963001776880944162612305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950669035841258883483073 2963001776880944162612305)
                    ·
                      refine ⟨2222251332660708121959229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963001776880944162612305 2222251332660708121959229)
                      ·
                        rfl

theorem cell23_4327819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 2, 2].length) (baseStart_4327819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327819 prefixEnd_4327819 := by exact prefixLift 4327819
  have htrace : WordTrace (prefixWord ++ tailWord_4327819) baseStart_4327819 baseEnd_4327819 := by
    simpa [prefixWord, tailWord_4327819, baseEnd_4327819] using wordTrace_append hprefix tailTrace_4327819
  have hstable : (prefixWord ++ tailWord_4327819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327819).length < 2 ^ (prefixWord ++ tailWord_4327819).sum := by decide
  have hdescent : baseEnd_4327819 < baseStart_4327819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327830 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4327830 : Nat := 118140960795 + 4327830 * 2 ^ 59
def prefixEnd_4327830 : Nat := 4983230072969 + 3 ^ 40 * 4327830 * 2
def baseEnd_4327830 : Nat := 2222256980947907578921679

theorem tailTrace_4327830 : CollatzResearch.WordTrace tailWord_4327830 prefixEnd_4327830 2222256980947907578921679 := by
  unfold tailWord_4327830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9865557994438657460225309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 105232618607345679575736629 9865557994438657460225309)
  ·
    refine ⟨3699584247914496547584491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9865557994438657460225309 3699584247914496547584491)
    ·
      refine ⟨5549376371871744821376737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3699584247914496547584491 5549376371871744821376737)
      ·
        refine ⟨4162032278903808616032553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5549376371871744821376737 4162032278903808616032553)
        ·
          refine ⟨3121524209177856462024415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4162032278903808616032553 3121524209177856462024415)
          ·
            refine ⟨4682286313766784693036623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121524209177856462024415 4682286313766784693036623)
            ·
              refine ⟨7023429470650177039554935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682286313766784693036623 7023429470650177039554935)
              ·
                refine ⟨10535144205975265559332403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7023429470650177039554935 10535144205975265559332403)
                ·
                  refine ⟨15802716308962898338998605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10535144205975265559332403 15802716308962898338998605)
                  ·
                    refine ⟨5926018615861086877124477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15802716308962898338998605 5926018615861086877124477)
                    ·
                      refine ⟨2222256980947907578921679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926018615861086877124477 2222256980947907578921679)
                      ·
                        rfl

theorem cell23_4327830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4327830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327830 prefixEnd_4327830 := by exact prefixLift 4327830
  have htrace : WordTrace (prefixWord ++ tailWord_4327830) baseStart_4327830 baseEnd_4327830 := by
    simpa [prefixWord, tailWord_4327830, baseEnd_4327830] using wordTrace_append hprefix tailTrace_4327830
  have hstable : (prefixWord ++ tailWord_4327830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327830).length < 2 ^ (prefixWord ++ tailWord_4327830).sum := by decide
  have hdescent : baseEnd_4327830 < baseStart_4327830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327876 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 5]
def baseStart_4327876 : Nat := 118140960795 + 4327876 * 2 ^ 59
def prefixEnd_4327876 : Nat := 4983230072969 + 3 ^ 40 * 4327876 * 2
def baseEnd_4327876 : Nat := 246920066784223822105163

theorem tailTrace_4327876 : CollatzResearch.WordTrace tailWord_4327876 prefixEnd_4327876 246920066784223822105163 := by
  unfold tailWord_4327876
  simp only [CollatzResearch.WordTrace]
  refine ⟨78925302834425934609889741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105233737112567912813186321 78925302834425934609889741)
  ·
    refine ⟨29596988562909725478708653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78925302834425934609889741 29596988562909725478708653)
    ·
      refine ⟨11098870711091147054515745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29596988562909725478708653 11098870711091147054515745)
      ·
        refine ⟨8324153033318360290886809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11098870711091147054515745 8324153033318360290886809)
        ·
          refine ⟨6243114774988770218165107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8324153033318360290886809 6243114774988770218165107)
          ·
            refine ⟨9364672162483155327247661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243114774988770218165107 9364672162483155327247661)
            ·
              refine ⟨3511752060931183247717873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9364672162483155327247661 3511752060931183247717873)
              ·
                refine ⟨2633814045698387435788405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511752060931183247717873 2633814045698387435788405)
                ·
                  refine ⟨246920066784223822105163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2633814045698387435788405 246920066784223822105163)
                  ·
                    rfl

theorem cell23_4327876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_4327876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327876 prefixEnd_4327876 := by exact prefixLift 4327876
  have htrace : WordTrace (prefixWord ++ tailWord_4327876) baseStart_4327876 baseEnd_4327876 := by
    simpa [prefixWord, tailWord_4327876, baseEnd_4327876] using wordTrace_append hprefix tailTrace_4327876
  have hstable : (prefixWord ++ tailWord_4327876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327876).length < 2 ^ (prefixWord ++ tailWord_4327876).sum := by decide
  have hdescent : baseEnd_4327876 < baseStart_4327876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327906 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4327906 : Nat := 118140960795 + 4327906 * 2 ^ 59
def prefixEnd_4327906 : Nat := 4983230072969 + 3 ^ 40 * 4327906 * 2
def baseEnd_4327906 : Nat := 740765335159216427190443

theorem tailTrace_4327906 : CollatzResearch.WordTrace tailWord_4327906 prefixEnd_4327906 740765335159216427190443 := by
  unfold tailWord_4327906
  simp only [CollatzResearch.WordTrace]
  refine ⟨39462924964685796085842893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105234466572495456228914381 39462924964685796085842893)
  ·
    refine ⟨14798596861757173532191085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39462924964685796085842893 14798596861757173532191085)
    ·
      refine ⟨5549473823158940074571657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14798596861757173532191085 5549473823158940074571657)
      ·
        refine ⟨4162105367369205055928743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5549473823158940074571657 4162105367369205055928743)
        ·
          refine ⟨6243158051053807583893115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4162105367369205055928743 6243158051053807583893115)
          ·
            refine ⟨9364737076580711375839673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243158051053807583893115 9364737076580711375839673)
            ·
              refine ⟨7023552807435533531879755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9364737076580711375839673 7023552807435533531879755)
              ·
                refine ⟨10535329211153300297819633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7023552807435533531879755 10535329211153300297819633)
                ·
                  refine ⟨7901496908364975223364725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10535329211153300297819633 7901496908364975223364725)
                  ·
                    refine ⟨740765335159216427190443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7901496908364975223364725 740765335159216427190443)
                    ·
                      rfl

theorem cell23_4327906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4327906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327906 prefixEnd_4327906 := by exact prefixLift 4327906
  have htrace : WordTrace (prefixWord ++ tailWord_4327906) baseStart_4327906 baseEnd_4327906 := by
    simpa [prefixWord, tailWord_4327906, baseEnd_4327906] using wordTrace_append hprefix tailTrace_4327906
  have hstable : (prefixWord ++ tailWord_4327906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327906).length < 2 ^ (prefixWord ++ tailWord_4327906).sum := by decide
  have hdescent : baseEnd_4327906 < baseStart_4327906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327909 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4327909 : Nat := 118140960795 + 4327909 * 2 ^ 59
def prefixEnd_4327909 : Nat := 4983230072969 + 3 ^ 40 * 4327909 * 2
def baseEnd_4327909 : Nat := 2222297545919612769833815

theorem tailTrace_4327909 : CollatzResearch.WordTrace tailWord_4327909 prefixEnd_4327909 2222297545919612769833815 := by
  unfold tailWord_4327909
  simp only [CollatzResearch.WordTrace]
  refine ⟨157851809277732315855730781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105234539518488210570487187 157851809277732315855730781)
  ·
    refine ⟨59194428479149618445899043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157851809277732315855730781 59194428479149618445899043)
    ·
      refine ⟨88791642718724427668848565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59194428479149618445899043 88791642718724427668848565)
      ·
        refine ⟨8324216504880415093954553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88791642718724427668848565 8324216504880415093954553)
        ·
          refine ⟨6243162378660311320465915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8324216504880415093954553 6243162378660311320465915)
          ·
            refine ⟨9364743567990466980698873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243162378660311320465915 9364743567990466980698873)
            ·
              refine ⟨7023557675992850235524155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9364743567990466980698873 7023557675992850235524155)
              ·
                refine ⟨10535336513989275353286233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7023557675992850235524155 10535336513989275353286233)
                ·
                  refine ⟨7901502385491956514964675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10535336513989275353286233 7901502385491956514964675)
                  ·
                    refine ⟨11852253578237934772447013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7901502385491956514964675 11852253578237934772447013)
                    ·
                      refine ⟨2222297545919612769833815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11852253578237934772447013 2222297545919612769833815)
                      ·
                        rfl

theorem cell23_4327909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4327909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327909 prefixEnd_4327909 := by exact prefixLift 4327909
  have htrace : WordTrace (prefixWord ++ tailWord_4327909) baseStart_4327909 baseEnd_4327909 := by
    simpa [prefixWord, tailWord_4327909, baseEnd_4327909] using wordTrace_append hprefix tailTrace_4327909
  have hstable : (prefixWord ++ tailWord_4327909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327909).length < 2 ^ (prefixWord ++ tailWord_4327909).sum := by decide
  have hdescent : baseEnd_4327909 < baseStart_4327909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327912 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4327912 : Nat := 118140960795 + 4327912 * 2 ^ 59
def prefixEnd_4327912 : Nat := 4983230072969 + 3 ^ 40 * 4327912 * 2
def baseEnd_4327912 : Nat := 2222299086361576258096301

theorem tailTrace_4327912 : CollatzResearch.WordTrace tailWord_4327912 prefixEnd_4327912 2222299086361576258096301 := by
  unfold tailWord_4327912
  simp only [CollatzResearch.WordTrace]
  refine ⟨78925959348360723684044995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105234612464480964912059993 78925959348360723684044995)
  ·
    refine ⟨118388939022541085526067493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78925959348360723684044995 118388939022541085526067493)
    ·
      refine ⟨22197926066726453536137655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118388939022541085526067493 22197926066726453536137655)
      ·
        refine ⟨33296889100089680304206483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22197926066726453536137655 33296889100089680304206483)
        ·
          refine ⟨49945333650134520456309725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33296889100089680304206483 49945333650134520456309725)
          ·
            refine ⟨18729500118800445171116147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49945333650134520456309725 18729500118800445171116147)
            ·
              refine ⟨28094250178200667756674221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18729500118800445171116147 28094250178200667756674221)
              ·
                refine ⟨10535343816825250408752833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28094250178200667756674221 10535343816825250408752833)
                ·
                  refine ⟨7901507862618937806564625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10535343816825250408752833 7901507862618937806564625)
                  ·
                    refine ⟨5926130896964203354923469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7901507862618937806564625 5926130896964203354923469)
                    ·
                      refine ⟨2222299086361576258096301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926130896964203354923469 2222299086361576258096301)
                      ·
                        rfl

theorem cell23_4327912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4327912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327912 prefixEnd_4327912 := by exact prefixLift 4327912
  have htrace : WordTrace (prefixWord ++ tailWord_4327912) baseStart_4327912 baseEnd_4327912 := by
    simpa [prefixWord, tailWord_4327912, baseEnd_4327912] using wordTrace_append hprefix tailTrace_4327912
  have hstable : (prefixWord ++ tailWord_4327912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327912).length < 2 ^ (prefixWord ++ tailWord_4327912).sum := by decide
  have hdescent : baseEnd_4327912 < baseStart_4327912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4327992 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 4, 4]
def baseStart_4327992 : Nat := 118140960795 + 4327992 * 2 ^ 59
def prefixEnd_4327992 : Nat := 4983230072969 + 3 ^ 40 * 4327992 * 2
def baseEnd_4327992 : Nat := 740780054937978648365311

theorem tailTrace_4327992 : CollatzResearch.WordTrace tailWord_4327992 prefixEnd_4327992 740780054937978648365311 := by
  unfold tailWord_4327992
  simp only [CollatzResearch.WordTrace]
  refine ⟨78927418268215810515501115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105236557690954414020668153 78927418268215810515501115)
  ·
    refine ⟨118391127402323715773251673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78927418268215810515501115 118391127402323715773251673)
    ·
      refine ⟨88793345551742786829938755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118391127402323715773251673 88793345551742786829938755)
      ·
        refine ⟨133190018327614180244908133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88793345551742786829938755 133190018327614180244908133)
        ·
          refine ⟨24973128436427658795920275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133190018327614180244908133 24973128436427658795920275)
          ·
            refine ⟨37459692654641488193880413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24973128436427658795920275 37459692654641488193880413)
            ·
              refine ⟨14047384745490558072705155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37459692654641488193880413 14047384745490558072705155)
              ·
                refine ⟨21071077118235837109057733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14047384745490558072705155 21071077118235837109057733)
                ·
                  refine ⟨3950826959669219457948325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21071077118235837109057733 3950826959669219457948325)
                  ·
                    refine ⟨740780054937978648365311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3950826959669219457948325 740780054937978648365311)
                    ·
                      rfl

theorem cell23_4327992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_4327992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4327992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4327992 prefixEnd_4327992 := by exact prefixLift 4327992
  have htrace : WordTrace (prefixWord ++ tailWord_4327992) baseStart_4327992 baseEnd_4327992 := by
    simpa [prefixWord, tailWord_4327992, baseEnd_4327992] using wordTrace_append hprefix tailTrace_4327992
  have hstable : (prefixWord ++ tailWord_4327992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4327992).length < 2 ^ (prefixWord ++ tailWord_4327992).sum := by decide
  have hdescent : baseEnd_4327992 < baseStart_4327992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4327992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328032 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_4328032 : Nat := 118140960795 + 4328032 * 2 ^ 59
def prefixEnd_4328032 : Nat := 4983230072969 + 3 ^ 40 * 4328032 * 2
def baseEnd_4328032 : Nat := 2222360704040115788595749

theorem tailTrace_4328032 : CollatzResearch.WordTrace tailWord_4328032 prefixEnd_4328032 2222360704040115788595749 := by
  unfold tailWord_4328032
  simp only [CollatzResearch.WordTrace]
  refine ⟨78928147728143353931229175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105237530304191138574972233 78928147728143353931229175)
  ·
    refine ⟨118392221592215030896843763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78928147728143353931229175 118392221592215030896843763)
    ·
      refine ⟨177588332388322546345265645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118392221592215030896843763 177588332388322546345265645)
      ·
        refine ⟨66595624645620954879474617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177588332388322546345265645 66595624645620954879474617)
        ·
          refine ⟨49946718484215716159605963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66595624645620954879474617 49946718484215716159605963)
          ·
            refine ⟨74920077726323574239408945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49946718484215716159605963 74920077726323574239408945)
            ·
              refine ⟨56190058294742680679556709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74920077726323574239408945 56190058294742680679556709)
              ·
                refine ⟨10535635930264252627416883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56190058294742680679556709 10535635930264252627416883)
                ·
                  refine ⟨15803453895396378941125325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10535635930264252627416883 15803453895396378941125325)
                  ·
                    refine ⟨5926295210773642102921997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15803453895396378941125325 5926295210773642102921997)
                    ·
                      refine ⟨2222360704040115788595749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926295210773642102921997 2222360704040115788595749)
                      ·
                        rfl

theorem cell23_4328032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_4328032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328032 prefixEnd_4328032 := by exact prefixLift 4328032
  have htrace : WordTrace (prefixWord ++ tailWord_4328032) baseStart_4328032 baseEnd_4328032 := by
    simpa [prefixWord, tailWord_4328032, baseEnd_4328032] using wordTrace_append hprefix tailTrace_4328032
  have hstable : (prefixWord ++ tailWord_4328032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328032).length < 2 ^ (prefixWord ++ tailWord_4328032).sum := by decide
  have hdescent : baseEnd_4328032 < baseStart_4328032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328033 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_4328033 : Nat := 118140960795 + 4328033 * 2 ^ 59
def prefixEnd_4328033 : Nat := 4983230072969 + 3 ^ 40 * 4328033 * 2
def baseEnd_4328033 : Nat := 2222361217520770284683245

theorem tailTrace_4328033 : CollatzResearch.WordTrace tailWord_4328033 prefixEnd_4328033 2222361217520770284683245 := by
  unfold tailWord_4328033
  simp only [CollatzResearch.WordTrace]
  refine ⟨157856331929283085033244753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105237554619522056688829835 157856331929283085033244753)
  ·
    refine ⟨118392248946962313774933565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157856331929283085033244753 118392248946962313774933565)
    ·
      refine ⟨44397093355110867665600087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118392248946962313774933565 44397093355110867665600087)
      ·
        refine ⟨66595640032666301498400131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44397093355110867665600087 66595640032666301498400131)
        ·
          refine ⟨99893460048999452247600197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66595640032666301498400131 99893460048999452247600197)
          ·
            refine ⟨18730023759187397296425037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99893460048999452247600197 18730023759187397296425037)
            ·
              refine ⟨7023758909695273986159389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18730023759187397296425037 7023758909695273986159389)
              ·
                refine ⟨2633909591135727744809771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7023758909695273986159389 2633909591135727744809771)
                ·
                  refine ⟨3950864386703591617214657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2633909591135727744809771 3950864386703591617214657)
                  ·
                    refine ⟨2963148290027693712910993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950864386703591617214657 2963148290027693712910993)
                    ·
                      refine ⟨2222361217520770284683245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963148290027693712910993 2222361217520770284683245)
                      ·
                        rfl

theorem cell23_4328033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_4328033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328033 prefixEnd_4328033 := by exact prefixLift 4328033
  have htrace : WordTrace (prefixWord ++ tailWord_4328033) baseStart_4328033 baseEnd_4328033 := by
    simpa [prefixWord, tailWord_4328033, baseEnd_4328033] using wordTrace_append hprefix tailTrace_4328033
  have hstable : (prefixWord ++ tailWord_4328033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328033).length < 2 ^ (prefixWord ++ tailWord_4328033).sum := by decide
  have hdescent : baseEnd_4328033 < baseStart_4328033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328050 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_4328050 : Nat := 118140960795 + 4328050 * 2 ^ 59
def prefixEnd_4328050 : Nat := 4983230072969 + 3 ^ 40 * 4328050 * 2
def baseEnd_4328050 : Nat := 2222369946691896718170667

theorem tailTrace_4328050 : CollatzResearch.WordTrace tailWord_4328050 prefixEnd_4328050 2222369946691896718170667 := by
  unfold tailWord_4328050
  simp only [CollatzResearch.WordTrace]
  refine ⟨39464237992555374234153401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105237967980147664624409069 39464237992555374234153401)
  ·
    refine ⟨29598178494416530675615051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39464237992555374234153401 29598178494416530675615051)
    ·
      refine ⟨44397267741624796013422577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29598178494416530675615051 44397267741624796013422577)
      ·
        refine ⟨33297950806218597010066933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44397267741624796013422577 33297950806218597010066933)
        ·
          refine ⟨3121682888082993469693775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33297950806218597010066933 3121682888082993469693775)
          ·
            refine ⟨4682524332124490204540663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3121682888082993469693775 4682524332124490204540663)
            ·
              refine ⟨7023786498186735306810995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682524332124490204540663 7023786498186735306810995)
              ·
                refine ⟨10535679747280102960216493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7023786498186735306810995 10535679747280102960216493)
                ·
                  refine ⟨3950879905230038610081185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10535679747280102960216493 3950879905230038610081185)
                  ·
                    refine ⟨2963159928922528957560889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3950879905230038610081185 2963159928922528957560889)
                    ·
                      refine ⟨2222369946691896718170667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963159928922528957560889 2222369946691896718170667)
                      ·
                        rfl

theorem cell23_4328050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_4328050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328050 prefixEnd_4328050 := by exact prefixLift 4328050
  have htrace : WordTrace (prefixWord ++ tailWord_4328050) baseStart_4328050 baseEnd_4328050 := by
    simpa [prefixWord, tailWord_4328050, baseEnd_4328050] using wordTrace_append hprefix tailTrace_4328050
  have hstable : (prefixWord ++ tailWord_4328050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328050).length < 2 ^ (prefixWord ++ tailWord_4328050).sum := by decide
  have hdescent : baseEnd_4328050 < baseStart_4328050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328089 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 1, 4, 2]
def baseStart_4328089 : Nat := 118140960795 + 4328089 * 2 ^ 59
def prefixEnd_4328089 : Nat := 4983230072969 + 3 ^ 40 * 4328089 * 2
def baseEnd_4328089 : Nat := 2222389972437422065582987

theorem tailTrace_4328089 : CollatzResearch.WordTrace tailWord_4328089 prefixEnd_4328089 2222389972437422065582987 := by
  unfold tailWord_4328089
  simp only [CollatzResearch.WordTrace]
  refine ⟨157858374417080206597283321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105238916278053471064855547 157858374417080206597283321)
  ·
    refine ⟨118393780812810154947962491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157858374417080206597283321 118393780812810154947962491)
    ·
      refine ⟨177590671219215232421943737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118393780812810154947962491 177590671219215232421943737)
      ·
        refine ⟨133193003414411424316457803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177590671219215232421943737 133193003414411424316457803)
        ·
          refine ⟨199789505121617136474686705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133193003414411424316457803 199789505121617136474686705)
          ·
            refine ⟨149842128841212852356015029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199789505121617136474686705 149842128841212852356015029)
            ·
              refine ⟨14047699578863704908376409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149842128841212852356015029 14047699578863704908376409)
              ·
                refine ⟨10535774684147778681282307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14047699578863704908376409 10535774684147778681282307)
                ·
                  refine ⟨15803662026221668021923461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10535774684147778681282307 15803662026221668021923461)
                  ·
                    refine ⟨2963186629916562754110649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15803662026221668021923461 2963186629916562754110649)
                    ·
                      refine ⟨2222389972437422065582987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963186629916562754110649 2222389972437422065582987)
                      ·
                        rfl

theorem cell23_4328089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_4328089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328089 prefixEnd_4328089 := by exact prefixLift 4328089
  have htrace : WordTrace (prefixWord ++ tailWord_4328089) baseStart_4328089 baseEnd_4328089 := by
    simpa [prefixWord, tailWord_4328089, baseEnd_4328089] using wordTrace_append hprefix tailTrace_4328089
  have hstable : (prefixWord ++ tailWord_4328089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328089).length < 2 ^ (prefixWord ++ tailWord_4328089).sum := by decide
  have hdescent : baseEnd_4328089 < baseStart_4328089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328105 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_4328105 : Nat := 118140960795 + 4328105 * 2 ^ 59
def prefixEnd_4328105 : Nat := 4983230072969 + 3 ^ 40 * 4328105 * 2
def baseEnd_4328105 : Nat := 2222398188127894002982913

theorem tailTrace_4328105 : CollatzResearch.WordTrace tailWord_4328105 prefixEnd_4328105 2222398188127894002982913 := by
  unfold tailWord_4328105
  simp only [CollatzResearch.WordTrace]
  refine ⟨157858957985022241329865769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105239305323348160886577179 157858957985022241329865769)
  ·
    refine ⟨118394218488766680997399327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157858957985022241329865769 118394218488766680997399327)
    ·
      refine ⟨177591327733150021496098991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118394218488766680997399327 177591327733150021496098991)
      ·
        refine ⟨266386991599725032244148487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177591327733150021496098991 266386991599725032244148487)
        ·
          refine ⟨399580487399587548366222731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266386991599725032244148487 399580487399587548366222731)
          ·
            refine ⟨599370731099381322549334097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399580487399587548366222731 599370731099381322549334097)
            ·
              refine ⟨449528048324535991912000573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599370731099381322549334097 449528048324535991912000573)
              ·
                refine ⟨168573018121700996967000215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449528048324535991912000573 168573018121700996967000215)
                ·
                  refine ⟨252859527182551495450500323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168573018121700996967000215 252859527182551495450500323)
                  ·
                    refine ⟨379289290773827243175750485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252859527182551495450500323 379289290773827243175750485)
                    ·
                      refine ⟨2222398188127894002982913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 379289290773827243175750485 2222398188127894002982913)
                      ·
                        rfl

theorem cell23_4328105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_4328105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328105 prefixEnd_4328105 := by exact prefixLift 4328105
  have htrace : WordTrace (prefixWord ++ tailWord_4328105) baseStart_4328105 baseEnd_4328105 := by
    simpa [prefixWord, tailWord_4328105, baseEnd_4328105] using wordTrace_append hprefix tailTrace_4328105
  have hstable : (prefixWord ++ tailWord_4328105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328105).length < 2 ^ (prefixWord ++ tailWord_4328105).sum := by decide
  have hdescent : baseEnd_4328105 < baseStart_4328105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328109 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_4328109 : Nat := 118140960795 + 4328109 * 2 ^ 59
def prefixEnd_4328109 : Nat := 4983230072969 + 3 ^ 40 * 4328109 * 2
def baseEnd_4328109 : Nat := 2222400242050511987332895

theorem tailTrace_4328109 : CollatzResearch.WordTrace tailWord_4328109 prefixEnd_4328109 2222400242050511987332895 := by
  unfold tailWord_4328109
  simp only [CollatzResearch.WordTrace]
  refine ⟨157859103877007750013011381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105239402584671833342007587 157859103877007750013011381)
  ·
    refine ⟨14799290988469476563719817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157859103877007750013011381 14799290988469476563719817)
    ·
      refine ⟨11099468241352107422789863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14799290988469476563719817 11099468241352107422789863)
      ·
        refine ⟨16649202362028161134184795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11099468241352107422789863 16649202362028161134184795)
        ·
          refine ⟨24973803543042241701277193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16649202362028161134184795 24973803543042241701277193)
          ·
            refine ⟨18730352657281681275957895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24973803543042241701277193 18730352657281681275957895)
            ·
              refine ⟨28095528985922521913936843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18730352657281681275957895 28095528985922521913936843)
              ·
                refine ⟨42143293478883782870905265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28095528985922521913936843 42143293478883782870905265)
                ·
                  refine ⟨31607470109162837153178949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42143293478883782870905265 31607470109162837153178949)
                  ·
                    refine ⟨5926400645468031966221053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31607470109162837153178949 5926400645468031966221053)
                    ·
                      refine ⟨2222400242050511987332895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926400645468031966221053 2222400242050511987332895)
                      ·
                        rfl

theorem cell23_4328109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_4328109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328109 prefixEnd_4328109 := by exact prefixLift 4328109
  have htrace : WordTrace (prefixWord ++ tailWord_4328109) baseStart_4328109 baseEnd_4328109 := by
    simpa [prefixWord, tailWord_4328109, baseEnd_4328109] using wordTrace_append hprefix tailTrace_4328109
  have hstable : (prefixWord ++ tailWord_4328109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328109).length < 2 ^ (prefixWord ++ tailWord_4328109).sum := by decide
  have hdescent : baseEnd_4328109 < baseStart_4328109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328119 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_4328119 : Nat := 118140960795 + 4328119 * 2 ^ 59
def prefixEnd_4328119 : Nat := 4983230072969 + 3 ^ 40 * 4328119 * 2
def baseEnd_4328119 : Nat := 2222405376857056948207849

theorem tailTrace_4328119 : CollatzResearch.WordTrace tailWord_4328119 prefixEnd_4328119 2222405376857056948207849 := by
  unfold tailWord_4328119
  simp only [CollatzResearch.WordTrace]
  refine ⟨157859468606971521720875411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105239645737981014480583607 157859468606971521720875411)
  ·
    refine ⟨236789202910457282581313117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157859468606971521720875411 236789202910457282581313117)
    ·
      refine ⟨88795951091421480967992419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236789202910457282581313117 88795951091421480967992419)
      ·
        refine ⟨133193926637132221451988629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88795951091421480967992419 133193926637132221451988629)
        ·
          refine ⟨6243465311115572880561967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133193926637132221451988629 6243465311115572880561967)
          ·
            refine ⟨9365197966673359320842951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243465311115572880561967 9365197966673359320842951)
            ·
              refine ⟨14047796950010038981264427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9365197966673359320842951 14047796950010038981264427)
              ·
                refine ⟨21071695425015058471896641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14047796950010038981264427 21071695425015058471896641)
                ·
                  refine ⟨15803771568761293853922481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21071695425015058471896641 15803771568761293853922481)
                  ·
                    refine ⟨11852828676570970390441861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15803771568761293853922481 11852828676570970390441861)
                    ·
                      refine ⟨2222405376857056948207849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11852828676570970390441861 2222405376857056948207849)
                      ·
                        rfl

theorem cell23_4328119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_4328119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328119 prefixEnd_4328119 := by exact prefixLift 4328119
  have htrace : WordTrace (prefixWord ++ tailWord_4328119) baseStart_4328119 baseEnd_4328119 := by
    simpa [prefixWord, tailWord_4328119, baseEnd_4328119] using wordTrace_append hprefix tailTrace_4328119
  have hstable : (prefixWord ++ tailWord_4328119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328119).length < 2 ^ (prefixWord ++ tailWord_4328119).sum := by decide
  have hdescent : baseEnd_4328119 < baseStart_4328119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328156 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4328156 : Nat := 118140960795 + 4328156 * 2 ^ 59
def prefixEnd_4328156 : Nat := 4983230072969 + 3 ^ 40 * 4328156 * 2
def baseEnd_4328156 : Nat := 2222424375641273303445179

theorem tailTrace_4328156 : CollatzResearch.WordTrace tailWord_4328156 prefixEnd_4328156 2222424375641273303445179 := by
  unfold tailWord_4328156
  simp only [CollatzResearch.WordTrace]
  refine ⟨78930409053918738519986161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105240545405224984693314881 78930409053918738519986161)
  ·
    refine ⟨59197806790439053889989621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78930409053918738519986161 59197806790439053889989621)
    ·
      refine ⟨5549794386603661302186527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59197806790439053889989621 5549794386603661302186527)
      ·
        refine ⟨8324691579905491953279791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5549794386603661302186527 8324691579905491953279791)
        ·
          refine ⟨12487037369858237929919687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8324691579905491953279791 12487037369858237929919687)
          ·
            refine ⟨18730556054787356894879531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12487037369858237929919687 18730556054787356894879531)
            ·
              refine ⟨28095834082181035342319297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18730556054787356894879531 28095834082181035342319297)
              ·
                refine ⟨21071875561635776506739473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28095834082181035342319297 21071875561635776506739473)
                ·
                  refine ⟨15803906671226832380054605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21071875561635776506739473 15803906671226832380054605)
                  ·
                    refine ⟨5926465001710062142520477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15803906671226832380054605 5926465001710062142520477)
                    ·
                      refine ⟨2222424375641273303445179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926465001710062142520477 2222424375641273303445179)
                      ·
                        rfl

theorem cell23_4328156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4328156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328156 prefixEnd_4328156 := by exact prefixLift 4328156
  have htrace : WordTrace (prefixWord ++ tailWord_4328156) baseStart_4328156 baseEnd_4328156 := by
    simpa [prefixWord, tailWord_4328156, baseEnd_4328156] using wordTrace_append hprefix tailTrace_4328156
  have hstable : (prefixWord ++ tailWord_4328156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328156).length < 2 ^ (prefixWord ++ tailWord_4328156).sum := by decide
  have hdescent : baseEnd_4328156 < baseStart_4328156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328189 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_4328189 : Nat := 118140960795 + 4328189 * 2 ^ 59
def prefixEnd_4328189 : Nat := 4983230072969 + 3 ^ 40 * 4328189 * 2
def baseEnd_4328189 : Nat := 740813773500957224777509

theorem tailTrace_4328189 : CollatzResearch.WordTrace tailWord_4328189 prefixEnd_4328189 740813773500957224777509 := by
  unfold tailWord_4328189
  simp only [CollatzResearch.WordTrace]
  refine ⟨157862021716717923675923621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105241347811145282450615747 157862021716717923675923621)
  ·
    refine ⟨29599129071884610689235679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157862021716717923675923621 29599129071884610689235679)
    ·
      refine ⟨44398693607826916033853519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29599129071884610689235679 44398693607826916033853519)
      ·
        refine ⟨66598040411740374050780279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44398693607826916033853519 66598040411740374050780279)
        ·
          refine ⟨99897060617610561076170419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66598040411740374050780279 99897060617610561076170419)
          ·
            refine ⟨149845590926415841614255629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99897060617610561076170419 149845590926415841614255629)
            ·
              refine ⟨56192096597405940605345861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149845590926415841614255629 56192096597405940605345861)
              ·
                refine ⟨10536018112013613863502349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56192096597405940605345861 10536018112013613863502349)
                ·
                  refine ⟨3951006792005105198813381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10536018112013613863502349 3951006792005105198813381)
                  ·
                    refine ⟨740813773500957224777509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951006792005105198813381 740813773500957224777509)
                    ·
                      rfl

theorem cell23_4328189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_4328189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328189 prefixEnd_4328189 := by exact prefixLift 4328189
  have htrace : WordTrace (prefixWord ++ tailWord_4328189) baseStart_4328189 baseEnd_4328189 := by
    simpa [prefixWord, tailWord_4328189, baseEnd_4328189] using wordTrace_append hprefix tailTrace_4328189
  have hstable : (prefixWord ++ tailWord_4328189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328189).length < 2 ^ (prefixWord ++ tailWord_4328189).sum := by decide
  have hdescent : baseEnd_4328189 < baseStart_4328189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328202 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_4328202 : Nat := 118140960795 + 4328202 * 2 ^ 59
def prefixEnd_4328202 : Nat := 4983230072969 + 3 ^ 40 * 4328202 * 2
def baseEnd_4328202 : Nat := 246938666194597791496663

theorem tailTrace_4328202 : CollatzResearch.WordTrace tailWord_4328202 prefixEnd_4328202 246938666194597791496663 := by
  unfold tailWord_4328202
  simp only [CollatzResearch.WordTrace]
  refine ⟨39465623966417706724036715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105241663910447217930764573 39465623966417706724036715)
  ·
    refine ⟨59198435949626560086055073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39465623966417706724036715 59198435949626560086055073)
    ·
      refine ⟨44398826962219920064541305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59198435949626560086055073 44398826962219920064541305)
      ·
        refine ⟨33299120221664940048405979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44398826962219920064541305 33299120221664940048405979)
        ·
          refine ⟨49948680332497410072608969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33299120221664940048405979 49948680332497410072608969)
          ·
            refine ⟨37461510249373057554456727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49948680332497410072608969 37461510249373057554456727)
            ·
              refine ⟨56192265374059586331685091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37461510249373057554456727 56192265374059586331685091)
              ·
                refine ⟨84288398061089379497527637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56192265374059586331685091 84288398061089379497527637)
                ·
                  refine ⟨246938666194597791496663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 84288398061089379497527637 246938666194597791496663)
                  ·
                    rfl

theorem cell23_4328202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_4328202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328202 prefixEnd_4328202 := by exact prefixLift 4328202
  have htrace : WordTrace (prefixWord ++ tailWord_4328202) baseStart_4328202 baseEnd_4328202 := by
    simpa [prefixWord, tailWord_4328202, baseEnd_4328202] using wordTrace_append hprefix tailTrace_4328202
  have hstable : (prefixWord ++ tailWord_4328202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328202).length < 2 ^ (prefixWord ++ tailWord_4328202).sum := by decide
  have hdescent : baseEnd_4328202 < baseStart_4328202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328263 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_4328263 : Nat := 118140960795 + 4328263 * 2 ^ 59
def prefixEnd_4328263 : Nat := 4983230072969 + 3 ^ 40 * 4328263 * 2
def baseEnd_4328263 : Nat := 2222479318071304384807187

theorem tailTrace_4328263 : CollatzResearch.WordTrace tailWord_4328263 prefixEnd_4328263 2222479318071304384807187 := by
  unfold tailWord_4328263
  simp only [CollatzResearch.WordTrace]
  refine ⟨157864720718449834314117443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105243147145633222876078295 157864720718449834314117443)
  ·
    refine ⟨236797081077674751471176165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157864720718449834314117443 236797081077674751471176165)
    ·
      refine ⟨44399452702064015900845531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236797081077674751471176165 44399452702064015900845531)
      ·
        refine ⟨66599179053096023851268297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44399452702064015900845531 66599179053096023851268297)
        ·
          refine ⟨49949384289822017888451223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66599179053096023851268297 49949384289822017888451223)
          ·
            refine ⟨74924076434733026832676835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49949384289822017888451223 74924076434733026832676835)
            ·
              refine ⟨112386114652099540249015253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74924076434733026832676835 112386114652099540249015253)
              ·
                refine ⟨2634049562158582974586295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112386114652099540249015253 2634049562158582974586295)
                ·
                  refine ⟨3951074343237874461879443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634049562158582974586295 3951074343237874461879443)
                  ·
                    refine ⟨5926611514856811692819165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3951074343237874461879443 5926611514856811692819165)
                    ·
                      refine ⟨2222479318071304384807187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926611514856811692819165 2222479318071304384807187)
                      ·
                        rfl

theorem cell23_4328263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_4328263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328263 prefixEnd_4328263 := by exact prefixLift 4328263
  have htrace : WordTrace (prefixWord ++ tailWord_4328263) baseStart_4328263 baseEnd_4328263 := by
    simpa [prefixWord, tailWord_4328263, baseEnd_4328263] using wordTrace_append hprefix tailTrace_4328263
  have hstable : (prefixWord ++ tailWord_4328263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328263).length < 2 ^ (prefixWord ++ tailWord_4328263).sum := by decide
  have hdescent : baseEnd_4328263 < baseStart_4328263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328296 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 1, 6]
def baseStart_4328296 : Nat := 118140960795 + 4328296 * 2 ^ 59
def prefixEnd_4328296 : Nat := 4983230072969 + 3 ^ 40 * 4328296 * 2
def baseEnd_4328296 : Nat := 740832087644300918564845

theorem tailTrace_4328296 : CollatzResearch.WordTrace tailWord_4328296 prefixEnd_4328296 740832087644300918564845 := by
  unfold tailWord_4328296
  simp only [CollatzResearch.WordTrace]
  refine ⟨78932962163665140475034371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105243949551553520633379161 78932962163665140475034371)
  ·
    refine ⟨118399443245497710712551557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78932962163665140475034371 118399443245497710712551557)
    ·
      refine ⟨22199895608530820758603417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118399443245497710712551557 22199895608530820758603417)
      ·
        refine ⟨16649921706398115568952563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22199895608530820758603417 16649921706398115568952563)
        ·
          refine ⟨24974882559597173353428845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16649921706398115568952563 24974882559597173353428845)
          ·
            refine ⟨9365580959848940007535817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24974882559597173353428845 9365580959848940007535817)
            ·
              refine ⟨7024185719886705005651863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9365580959848940007535817 7024185719886705005651863)
              ·
                refine ⟨10536278579830057508477795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7024185719886705005651863 10536278579830057508477795)
                ·
                  refine ⟨15804417869745086262716693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10536278579830057508477795 15804417869745086262716693)
                  ·
                    refine ⟨740832087644300918564845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15804417869745086262716693 740832087644300918564845)
                    ·
                      rfl

theorem cell23_4328296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_4328296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328296 prefixEnd_4328296 := by exact prefixLift 4328296
  have htrace : WordTrace (prefixWord ++ tailWord_4328296) baseStart_4328296 baseEnd_4328296 := by
    simpa [prefixWord, tailWord_4328296, baseEnd_4328296] using wordTrace_append hprefix tailTrace_4328296
  have hstable : (prefixWord ++ tailWord_4328296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328296).length < 2 ^ (prefixWord ++ tailWord_4328296).sum := by decide
  have hdescent : baseEnd_4328296 < baseStart_4328296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328299 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4]
def baseStart_4328299 : Nat := 118140960795 + 4328299 * 2 ^ 59
def prefixEnd_4328299 : Nat := 4983230072969 + 3 ^ 40 * 4328299 * 2
def baseEnd_4328299 : Nat := 2222497803374866243957021

theorem tailTrace_4328299 : CollatzResearch.WordTrace tailWord_4328299 prefixEnd_4328299 2222497803374866243957021 := by
  unfold tailWord_4328299
  simp only [CollatzResearch.WordTrace]
  refine ⟨157866033746319412462427951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105244022497546274974951967 157866033746319412462427951)
  ·
    refine ⟨236799050619479118693641927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157866033746319412462427951 236799050619479118693641927)
    ·
      refine ⟨355198575929218678040462891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236799050619479118693641927 355198575929218678040462891)
      ·
        refine ⟨532797863893828017060694337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355198575929218678040462891 532797863893828017060694337)
        ·
          refine ⟨399598397920371012795520753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532797863893828017060694337 399598397920371012795520753)
          ·
            refine ⟨299698798440278259596640565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399598397920371012795520753 299698798440278259596640565)
            ·
              refine ⟨28096762353776086837185053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 299698798440278259596640565 28096762353776086837185053)
              ·
                refine ⟨10536285882666032563944395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28096762353776086837185053 10536285882666032563944395)
                ·
                  refine ⟨15804428823999048845916593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10536285882666032563944395 15804428823999048845916593)
                  ·
                    refine ⟨11853321617999286634437445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15804428823999048845916593 11853321617999286634437445)
                    ·
                      refine ⟨2222497803374866243957021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11853321617999286634437445 2222497803374866243957021)
                      ·
                        rfl

theorem cell23_4328299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].length) (baseStart_4328299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328299 prefixEnd_4328299 := by exact prefixLift 4328299
  have htrace : WordTrace (prefixWord ++ tailWord_4328299) baseStart_4328299 baseEnd_4328299 := by
    simpa [prefixWord, tailWord_4328299, baseEnd_4328299] using wordTrace_append hprefix tailTrace_4328299
  have hstable : (prefixWord ++ tailWord_4328299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328299).length < 2 ^ (prefixWord ++ tailWord_4328299).sum := by decide
  have hdescent : baseEnd_4328299 < baseStart_4328299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328306 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_4328306 : Nat := 118140960795 + 4328306 * 2 ^ 59
def prefixEnd_4328306 : Nat := 4983230072969 + 3 ^ 40 * 4328306 * 2
def baseEnd_4328306 : Nat := 2222501397739447716569489

theorem tailTrace_4328306 : CollatzResearch.WordTrace tailWord_4328306 prefixEnd_4328306 2222501397739447716569489 := by
  unfold tailWord_4328306
  simp only [CollatzResearch.WordTrace]
  refine ⟨39466572264323513164483193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105244192704862701771955181 39466572264323513164483193)
  ·
    refine ⟨29599929198242634873362395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39466572264323513164483193 29599929198242634873362395)
    ·
      refine ⟨44399893797363952310043593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29599929198242634873362395 44399893797363952310043593)
      ·
        refine ⟨33299920348022964232532695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44399893797363952310043593 33299920348022964232532695)
        ·
          refine ⟨49949880522034446348799043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33299920348022964232532695 49949880522034446348799043)
          ·
            refine ⟨74924820783051669523198565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49949880522034446348799043 74924820783051669523198565)
            ·
              refine ⟨14048403896822188035599731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74924820783051669523198565 14048403896822188035599731)
              ·
                refine ⟨21072605845233282053399597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14048403896822188035599731 21072605845233282053399597)
                ·
                  refine ⟨7902227191962480770024849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21072605845233282053399597 7902227191962480770024849)
                  ·
                    refine ⟨5926670393971860577518637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7902227191962480770024849 5926670393971860577518637)
                    ·
                      refine ⟨2222501397739447716569489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926670393971860577518637 2222501397739447716569489)
                      ·
                        rfl

theorem cell23_4328306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_4328306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328306 prefixEnd_4328306 := by exact prefixLift 4328306
  have htrace : WordTrace (prefixWord ++ tailWord_4328306) baseStart_4328306 baseEnd_4328306 := by
    simpa [prefixWord, tailWord_4328306, baseEnd_4328306] using wordTrace_append hprefix tailTrace_4328306
  have hstable : (prefixWord ++ tailWord_4328306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328306).length < 2 ^ (prefixWord ++ tailWord_4328306).sum := by decide
  have hdescent : baseEnd_4328306 < baseStart_4328306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328330 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_4328330 : Nat := 118140960795 + 4328330 * 2 ^ 59
def prefixEnd_4328330 : Nat := 4983230072969 + 3 ^ 40 * 4328330 * 2
def baseEnd_4328330 : Nat := 740837907091718540889793

theorem tailTrace_4328330 : CollatzResearch.WordTrace tailWord_4328330 prefixEnd_4328330 740837907091718540889793 := by
  unfold tailWord_4328330
  simp only [CollatzResearch.WordTrace]
  refine ⟨39466791102301776189201611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105244776272804736504537629 39466791102301776189201611)
  ·
    refine ⟨59200186653452664283802417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39466791102301776189201611 59200186653452664283802417)
    ·
      refine ⟨44400139990089498212851813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59200186653452664283802417 44400139990089498212851813)
      ·
        refine ⟨8325026248141780914909715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44400139990089498212851813 8325026248141780914909715)
        ·
          refine ⟨12487539372212671372364573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8325026248141780914909715 12487539372212671372364573)
          ·
            refine ⟨4682827264579751764636715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12487539372212671372364573 4682827264579751764636715)
            ·
              refine ⟨7024240896869627646955073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4682827264579751764636715 7024240896869627646955073)
              ·
                refine ⟨5268180672652220735216305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7024240896869627646955073 5268180672652220735216305)
                ·
                  refine ⟨3951135504489165551412229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5268180672652220735216305 3951135504489165551412229)
                  ·
                    refine ⟨740837907091718540889793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951135504489165551412229 740837907091718540889793)
                    ·
                      rfl

theorem cell23_4328330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_4328330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328330 prefixEnd_4328330 := by exact prefixLift 4328330
  have htrace : WordTrace (prefixWord ++ tailWord_4328330) baseStart_4328330 baseEnd_4328330 := by
    simpa [prefixWord, tailWord_4328330, baseEnd_4328330] using wordTrace_append hprefix tailTrace_4328330
  have hstable : (prefixWord ++ tailWord_4328330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328330).length < 2 ^ (prefixWord ++ tailWord_4328330).sum := by decide
  have hdescent : baseEnd_4328330 < baseStart_4328330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328353 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4328353 : Nat := 118140960795 + 4328353 * 2 ^ 59
def prefixEnd_4328353 : Nat := 4983230072969 + 3 ^ 40 * 4328353 * 2
def baseEnd_4328353 : Nat := 2222525531330209032681773

theorem tailTrace_4328353 : CollatzResearch.WordTrace tailWord_4328353 prefixEnd_4328353 2222525531330209032681773 := by
  unfold tailWord_4328353
  simp only [CollatzResearch.WordTrace]
  refine ⟨157868003288123779684893713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105245335525415853123262475 157868003288123779684893713)
  ·
    refine ⟨118401002466092834763670285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157868003288123779684893713 118401002466092834763670285)
    ·
      refine ⟨44400375924784813036376357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118401002466092834763670285 44400375924784813036376357)
      ·
        refine ⟨8325070485897152444320567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44400375924784813036376357 8325070485897152444320567)
        ·
          refine ⟨12487605728845728666480851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8325070485897152444320567 12487605728845728666480851)
          ·
            refine ⟨18731408593268592999721277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12487605728845728666480851 18731408593268592999721277)
            ·
              refine ⟨7024278222475722374895479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18731408593268592999721277 7024278222475722374895479)
              ·
                refine ⟨10536417333713583562343219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7024278222475722374895479 10536417333713583562343219)
                ·
                  refine ⟨15804626000570375343514829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10536417333713583562343219 15804626000570375343514829)
                  ·
                    refine ⟨5926734750213890753818061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15804626000570375343514829 5926734750213890753818061)
                    ·
                      refine ⟨2222525531330209032681773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926734750213890753818061 2222525531330209032681773)
                      ·
                        rfl

theorem cell23_4328353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4328353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328353 prefixEnd_4328353 := by exact prefixLift 4328353
  have htrace : WordTrace (prefixWord ++ tailWord_4328353) baseStart_4328353 baseEnd_4328353 := by
    simpa [prefixWord, tailWord_4328353, baseEnd_4328353] using wordTrace_append hprefix tailTrace_4328353
  have hstable : (prefixWord ++ tailWord_4328353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328353).length < 2 ^ (prefixWord ++ tailWord_4328353).sum := by decide
  have hdescent : baseEnd_4328353 < baseStart_4328353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328396 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4328396 : Nat := 118140960795 + 4328396 * 2 ^ 59
def prefixEnd_4328396 : Nat := 4983230072969 + 3 ^ 40 * 4328396 * 2
def baseEnd_4328396 : Nat := 2222547610998352364444075

theorem tailTrace_4328396 : CollatzResearch.WordTrace tailWord_4328396 prefixEnd_4328396 2222547610998352364444075 := by
  unfold tailWord_4328396
  simp only [CollatzResearch.WordTrace]
  refine ⟨78934785813483999014354521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105246381084645332019139361 78934785813483999014354521)
  ·
    refine ⟨59201089360112999260765891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78934785813483999014354521 59201089360112999260765891)
    ·
      refine ⟨88801634040169498891148837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59201089360112999260765891 88801634040169498891148837)
      ·
        refine ⟨16650306382531781042090407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88801634040169498891148837 16650306382531781042090407)
        ·
          refine ⟨24975459573797671563135611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16650306382531781042090407 24975459573797671563135611)
          ·
            refine ⟨37463189360696507344703417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24975459573797671563135611 37463189360696507344703417)
            ·
              refine ⟨28097392020522380508527563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37463189360696507344703417 28097392020522380508527563)
              ·
                refine ⟨42146088030783570762791345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28097392020522380508527563 42146088030783570762791345)
                ·
                  refine ⟨31609566023087678072093509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42146088030783570762791345 31609566023087678072093509)
                  ·
                    refine ⟨5926793629328939638517533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31609566023087678072093509 5926793629328939638517533)
                    ·
                      refine ⟨2222547610998352364444075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5926793629328939638517533 2222547610998352364444075)
                      ·
                        rfl

theorem cell23_4328396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4328396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328396 prefixEnd_4328396 := by exact prefixLift 4328396
  have htrace : WordTrace (prefixWord ++ tailWord_4328396) baseStart_4328396 baseEnd_4328396 := by
    simpa [prefixWord, tailWord_4328396, baseEnd_4328396] using wordTrace_append hprefix tailTrace_4328396
  have hstable : (prefixWord ++ tailWord_4328396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328396).length < 2 ^ (prefixWord ++ tailWord_4328396).sum := by decide
  have hdescent : baseEnd_4328396 < baseStart_4328396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328456 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_4328456 : Nat := 118140960795 + 4328456 * 2 ^ 59
def prefixEnd_4328456 : Nat := 4983230072969 + 3 ^ 40 * 4328456 * 2
def baseEnd_4328456 : Nat := 2222578419837622129693799

theorem tailTrace_4328456 : CollatzResearch.WordTrace tailWord_4328456 prefixEnd_4328456 2222578419837622129693799 := by
  unfold tailWord_4328456
  simp only [CollatzResearch.WordTrace]
  refine ⟨78935880003375314137946611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105247840004500418850595481 78935880003375314137946611)
  ·
    refine ⟨118403820005062971206919917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78935880003375314137946611 118403820005062971206919917)
    ·
      refine ⟨44401432501898614202594969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118403820005062971206919917 44401432501898614202594969)
      ·
        refine ⟨33301074376423960651946227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44401432501898614202594969 33301074376423960651946227)
        ·
          refine ⟨49951611564635940977919341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33301074376423960651946227 49951611564635940977919341)
          ·
            refine ⟨18731854336738477866719753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49951611564635940977919341 18731854336738477866719753)
            ·
              refine ⟨14048890752553858400039815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18731854336738477866719753 14048890752553858400039815)
              ·
                refine ⟨21073336128830787600059723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14048890752553858400039815 21073336128830787600059723)
                ·
                  refine ⟨31610004193246181400089585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21073336128830787600059723 31610004193246181400089585)
                  ·
                    refine ⟨23707503144934636050067189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31610004193246181400089585 23707503144934636050067189)
                    ·
                      refine ⟨2222578419837622129693799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23707503144934636050067189 2222578419837622129693799)
                      ·
                        rfl

theorem cell23_4328456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_4328456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328456 prefixEnd_4328456 := by exact prefixLift 4328456
  have htrace : WordTrace (prefixWord ++ tailWord_4328456) baseStart_4328456 baseEnd_4328456 := by
    simpa [prefixWord, tailWord_4328456, baseEnd_4328456] using wordTrace_append hprefix tailTrace_4328456
  have hstable : (prefixWord ++ tailWord_4328456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328456).length < 2 ^ (prefixWord ++ tailWord_4328456).sum := by decide
  have hdescent : baseEnd_4328456 < baseStart_4328456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328483 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 4]
def baseStart_4328483 : Nat := 118140960795 + 4328483 * 2 ^ 59
def prefixEnd_4328483 : Nat := 4983230072969 + 3 ^ 40 * 4328483 * 2
def baseEnd_4328483 : Nat := 2222592283815293524056175

theorem tailTrace_4328483 : CollatzResearch.WordTrace tailWord_4328483 prefixEnd_4328483 2222592283815293524056175 := by
  unfold tailWord_4328483
  simp only [CollatzResearch.WordTrace]
  refine ⟨157872744777652811887126103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105248496518435207924750735 157872744777652811887126103)
  ·
    refine ⟨236809117166479217830689155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157872744777652811887126103 236809117166479217830689155)
    ·
      refine ⟨355213675749718826746033733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236809117166479217830689155 355213675749718826746033733)
      ·
        refine ⟨66602564203072280014881325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 355213675749718826746033733 66602564203072280014881325)
        ·
          refine ⟨24975961576152105005580497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66602564203072280014881325 24975961576152105005580497)
          ·
            refine ⟨18731971182114078754185373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24975961576152105005580497 18731971182114078754185373)
            ·
              refine ⟨7024489193292779532819515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18731971182114078754185373 7024489193292779532819515)
              ·
                refine ⟨10536733789939169299229273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7024489193292779532819515 10536733789939169299229273)
                ·
                  refine ⟨7902550342454376974421955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10536733789939169299229273 7902550342454376974421955)
                  ·
                    refine ⟨11853825513681565461632933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7902550342454376974421955 11853825513681565461632933)
                    ·
                      refine ⟨2222592283815293524056175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11853825513681565461632933 2222592283815293524056175)
                      ·
                        rfl

theorem cell23_4328483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_4328483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328483 prefixEnd_4328483 := by exact prefixLift 4328483
  have htrace : WordTrace (prefixWord ++ tailWord_4328483) baseStart_4328483 baseEnd_4328483 := by
    simpa [prefixWord, tailWord_4328483, baseEnd_4328483] using wordTrace_append hprefix tailTrace_4328483
  have hstable : (prefixWord ++ tailWord_4328483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328483).length < 2 ^ (prefixWord ++ tailWord_4328483).sum := by decide
  have hdescent : baseEnd_4328483 < baseStart_4328483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328510 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_4328510 : Nat := 118140960795 + 4328510 * 2 ^ 59
def prefixEnd_4328510 : Nat := 4983230072969 + 3 ^ 40 * 4328510 * 2
def baseEnd_4328510 : Nat := 740868715930988306139517

theorem tailTrace_4328510 : CollatzResearch.WordTrace tailWord_4328510 prefixEnd_4328510 740868715930988306139517 := by
  unfold tailWord_4328510
  simp only [CollatzResearch.WordTrace]
  refine ⟨19734216193569374437294873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105249153032369996998905989 19734216193569374437294873)
  ·
    refine ⟨14800662145177030827971155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19734216193569374437294873 14800662145177030827971155)
    ·
      refine ⟨22200993217765546241956733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14800662145177030827971155 22200993217765546241956733)
      ·
        refine ⟨8325372456662079840733775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22200993217765546241956733 8325372456662079840733775)
        ·
          refine ⟨12488058684993119761100663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8325372456662079840733775 12488058684993119761100663)
          ·
            refine ⟨18732088027489679641650995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12488058684993119761100663 18732088027489679641650995)
            ·
              refine ⟨28098132041234519462476493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18732088027489679641650995 28098132041234519462476493)
              ·
                refine ⟨10536799515462944798428685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28098132041234519462476493 10536799515462944798428685)
                ·
                  refine ⟨3951299818298604299410757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10536799515462944798428685 3951299818298604299410757)
                  ·
                    refine ⟨740868715930988306139517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951299818298604299410757 740868715930988306139517)
                    ·
                      rfl

theorem cell23_4328510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_4328510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328510 prefixEnd_4328510 := by exact prefixLift 4328510
  have htrace : WordTrace (prefixWord ++ tailWord_4328510) baseStart_4328510 baseEnd_4328510 := by
    simpa [prefixWord, tailWord_4328510, baseEnd_4328510] using wordTrace_append hprefix tailTrace_4328510
  have hstable : (prefixWord ++ tailWord_4328510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328510).length < 2 ^ (prefixWord ++ tailWord_4328510).sum := by decide
  have hdescent : baseEnd_4328510 < baseStart_4328510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328526 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_4328526 : Nat := 118140960795 + 4328526 * 2 ^ 59
def prefixEnd_4328526 : Nat := 4983230072969 + 3 ^ 40 * 4328526 * 2
def baseEnd_4328526 : Nat := 2222614363483436855818477

theorem tailTrace_4328526 : CollatzResearch.WordTrace tailWord_4328526 prefixEnd_4328526 2222614363483436855818477 := by
  unfold tailWord_4328526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19734289139562128778867679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105249542077664686820627621 19734289139562128778867679)
  ·
    refine ⟨29601433709343193168301519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19734289139562128778867679 29601433709343193168301519)
    ·
      refine ⟨44402150564014789752452279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29601433709343193168301519 44402150564014789752452279)
      ·
        refine ⟨66603225846022184628678419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44402150564014789752452279 66603225846022184628678419)
        ·
          refine ⟨99904838769033276943017629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66603225846022184628678419 99904838769033276943017629)
          ·
            refine ⟨37464314538387478853631611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99904838769033276943017629 37464314538387478853631611)
            ·
              refine ⟨56196471807581218280447417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37464314538387478853631611 56196471807581218280447417)
              ·
                refine ⟨42147353855685913710335563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56196471807581218280447417 42147353855685913710335563)
                ·
                  refine ⟨63221030783528870565503345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42147353855685913710335563 63221030783528870565503345)
                  ·
                    refine ⟨47415773087646652924127509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63221030783528870565503345 47415773087646652924127509)
                    ·
                      refine ⟨2222614363483436855818477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47415773087646652924127509 2222614363483436855818477)
                      ·
                        rfl

theorem cell23_4328526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_4328526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328526 prefixEnd_4328526 := by exact prefixLift 4328526
  have htrace : WordTrace (prefixWord ++ tailWord_4328526) baseStart_4328526 baseEnd_4328526 := by
    simpa [prefixWord, tailWord_4328526, baseEnd_4328526] using wordTrace_append hprefix tailTrace_4328526
  have hstable : (prefixWord ++ tailWord_4328526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328526).length < 2 ^ (prefixWord ++ tailWord_4328526).sum := by decide
  have hdescent : baseEnd_4328526 < baseStart_4328526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328543 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 1, 5, 2]
def baseStart_4328543 : Nat := 118140960795 + 4328543 * 2 ^ 59
def prefixEnd_4328543 : Nat := 4983230072969 + 3 ^ 40 * 4328543 * 2
def baseEnd_4328543 : Nat := 2222623092654563289305899

theorem tailTrace_4328543 : CollatzResearch.WordTrace tailWord_4328543 prefixEnd_4328543 2222623092654563289305899 := by
  unfold tailWord_4328543
  simp only [CollatzResearch.WordTrace]
  refine ⟨157874933157435442134310283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105249955438290294756206855 157874933157435442134310283)
  ·
    refine ⟨236812399736153163201465425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157874933157435442134310283 236812399736153163201465425)
    ·
      refine ⟨177609299802114872401099069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236812399736153163201465425 177609299802114872401099069)
      ·
        refine ⟨66603487425793077150412151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177609299802114872401099069 66603487425793077150412151)
        ·
          refine ⟨99905231138689615725618227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66603487425793077150412151 99905231138689615725618227)
          ·
            refine ⟨149857846708034423588427341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99905231138689615725618227 149857846708034423588427341)
            ·
              refine ⟨56196692515512908845660253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149857846708034423588427341 56196692515512908845660253)
              ·
                refine ⟨21073759693317340817122595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56196692515512908845660253 21073759693317340817122595)
                ·
                  refine ⟨31610639539976011225683893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21073759693317340817122595 31610639539976011225683893)
                  ·
                    refine ⟨2963497456872751052407865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31610639539976011225683893 2963497456872751052407865)
                    ·
                      refine ⟨2222623092654563289305899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963497456872751052407865 2222623092654563289305899)
                      ·
                        rfl

theorem cell23_4328543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_4328543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328543 prefixEnd_4328543 := by exact prefixLift 4328543
  have htrace : WordTrace (prefixWord ++ tailWord_4328543) baseStart_4328543 baseEnd_4328543 := by
    simpa [prefixWord, tailWord_4328543, baseEnd_4328543] using wordTrace_append hprefix tailTrace_4328543
  have hstable : (prefixWord ++ tailWord_4328543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328543).length < 2 ^ (prefixWord ++ tailWord_4328543).sum := by decide
  have hdescent : baseEnd_4328543 < baseStart_4328543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328553 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 1, 5]
def baseStart_4328553 : Nat := 118140960795 + 4328553 * 2 ^ 59
def prefixEnd_4328553 : Nat := 4983230072969 + 3 ^ 40 * 4328553 * 2
def baseEnd_4328553 : Nat := 740876075820369416726951

theorem tailTrace_4328553 : CollatzResearch.WordTrace tailWord_4328553 prefixEnd_4328553 740876075820369416726951 := by
  unfold tailWord_4328553
  simp only [CollatzResearch.WordTrace]
  refine ⟨157875297887399213842174313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105250198591599475894782875 157875297887399213842174313)
  ·
    refine ⟨118406473415549410381630735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157875297887399213842174313 118406473415549410381630735)
    ·
      refine ⟨177609710123324115572446103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118406473415549410381630735 177609710123324115572446103)
      ·
        refine ⟨266414565184986173358669155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177609710123324115572446103 266414565184986173358669155)
        ·
          refine ⟨399621847777479260038003733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266414565184986173358669155 399621847777479260038003733)
          ·
            refine ⟨18732274114569340314281425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 399621847777479260038003733 18732274114569340314281425)
            ·
              refine ⟨14049205585927005235711069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18732274114569340314281425 14049205585927005235711069)
              ·
                refine ⟨5268452094722626963391651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14049205585927005235711069 5268452094722626963391651)
                ·
                  refine ⟨7902678142083940445087477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268452094722626963391651 7902678142083940445087477)
                  ·
                    refine ⟨740876075820369416726951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7902678142083940445087477 740876075820369416726951)
                    ·
                      rfl

theorem cell23_4328553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_4328553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328553 prefixEnd_4328553 := by exact prefixLift 4328553
  have htrace : WordTrace (prefixWord ++ tailWord_4328553) baseStart_4328553 baseEnd_4328553 := by
    simpa [prefixWord, tailWord_4328553, baseEnd_4328553] using wordTrace_append hprefix tailTrace_4328553
  have hstable : (prefixWord ++ tailWord_4328553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328553).length < 2 ^ (prefixWord ++ tailWord_4328553).sum := by decide
  have hdescent : baseEnd_4328553 < baseStart_4328553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328560 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 2, 3, 2]
def baseStart_4328560 : Nat := 118140960795 + 4328560 * 2 ^ 59
def prefixEnd_4328560 : Nat := 4983230072969 + 3 ^ 40 * 4328560 * 2
def baseEnd_4328560 : Nat := 2222631821825689722793321

theorem tailTrace_4328560 : CollatzResearch.WordTrace tailWord_4328560 prefixEnd_4328560 2222631821825689722793321 := by
  unfold tailWord_4328560
  simp only [CollatzResearch.WordTrace]
  refine ⟨78937776599186927018839567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105250368798915902691786089 78937776599186927018839567)
  ·
    refine ⟨118406664898780390528259351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78937776599186927018839567 118406664898780390528259351)
    ·
      refine ⟨177609997348170585792389027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118406664898780390528259351 177609997348170585792389027)
      ·
        refine ⟨266414996022255878688583541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177609997348170585792389027 266414996022255878688583541)
        ·
          refine ⟨24976405877086488627054707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 266414996022255878688583541 24976405877086488627054707)
          ·
            refine ⟨37464608815629732940582061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24976405877086488627054707 37464608815629732940582061)
            ·
              refine ⟨14049228305861149852718273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37464608815629732940582061 14049228305861149852718273)
              ·
                refine ⟨10536921229395862389538705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14049228305861149852718273 10536921229395862389538705)
                ·
                  refine ⟨7902690922046896792154029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10536921229395862389538705 7902690922046896792154029)
                  ·
                    refine ⟨2963509095767586297057761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7902690922046896792154029 2963509095767586297057761)
                    ·
                      refine ⟨2222631821825689722793321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963509095767586297057761 2222631821825689722793321)
                      ·
                        rfl

theorem cell23_4328560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 2, 3, 2].length) (baseStart_4328560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328560 prefixEnd_4328560 := by exact prefixLift 4328560
  have htrace : WordTrace (prefixWord ++ tailWord_4328560) baseStart_4328560 baseEnd_4328560 := by
    simpa [prefixWord, tailWord_4328560, baseEnd_4328560] using wordTrace_append hprefix tailTrace_4328560
  have hstable : (prefixWord ++ tailWord_4328560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328560).length < 2 ^ (prefixWord ++ tailWord_4328560).sum := by decide
  have hdescent : baseEnd_4328560 < baseStart_4328560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328573 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_4328573 : Nat := 118140960795 + 4328573 * 2 ^ 59
def prefixEnd_4328573 : Nat := 4983230072969 + 3 ^ 40 * 4328573 * 2
def baseEnd_4328573 : Nat := 2222638497074198171930761

theorem tailTrace_4328573 : CollatzResearch.WordTrace tailWord_4328573 prefixEnd_4328573 2222638497074198171930761 := by
  unfold tailWord_4328573
  simp only [CollatzResearch.WordTrace]
  refine ⟨157876027347326757257902373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105250684898217838171934915 157876027347326757257902373)
  ·
    refine ⟨29601755127623766985856695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157876027347326757257902373 29601755127623766985856695)
    ·
      refine ⟨44402632691435650478785043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29601755127623766985856695 44402632691435650478785043)
      ·
        refine ⟨66603949037153475718177565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44402632691435650478785043 66603949037153475718177565)
        ·
          refine ⟨24976480888932553394316587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66603949037153475718177565 24976480888932553394316587)
          ·
            refine ⟨37464721333398830091474881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24976480888932553394316587 37464721333398830091474881)
            ·
              refine ⟨28098541000049122568606161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37464721333398830091474881 28098541000049122568606161)
              ·
                refine ⟨21073905750036841926454621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28098541000049122568606161 21073905750036841926454621)
                ·
                  refine ⟨7902714656263815722420483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21073905750036841926454621 7902714656263815722420483)
                  ·
                    refine ⟨11854071984395723583630725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7902714656263815722420483 11854071984395723583630725)
                    ·
                      refine ⟨2222638497074198171930761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11854071984395723583630725 2222638497074198171930761)
                      ·
                        rfl

theorem cell23_4328573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_4328573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328573 prefixEnd_4328573 := by exact prefixLift 4328573
  have htrace : WordTrace (prefixWord ++ tailWord_4328573) baseStart_4328573 baseEnd_4328573 := by
    simpa [prefixWord, tailWord_4328573, baseEnd_4328573] using wordTrace_append hprefix tailTrace_4328573
  have hstable : (prefixWord ++ tailWord_4328573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328573).length < 2 ^ (prefixWord ++ tailWord_4328573).sum := by decide
  have hdescent : baseEnd_4328573 < baseStart_4328573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328574 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_4328574 : Nat := 118140960795 + 4328574 * 2 ^ 59
def prefixEnd_4328574 : Nat := 4983230072969 + 3 ^ 40 * 4328574 * 2
def baseEnd_4328574 : Nat := 246959890061650296446473

theorem tailTrace_4328574 : CollatzResearch.WordTrace tailWord_4328574 prefixEnd_4328574 246959890061650296446473 := by
  unfold tailWord_4328574
  simp only [CollatzResearch.WordTrace]
  refine ⟨19734507977540391803586097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105250709213548756285792517 19734507977540391803586097)
  ·
    refine ⟨14800880983155293852689573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19734507977540391803586097 14800880983155293852689573)
    ·
      refine ⟨2775165184341617597379295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14800880983155293852689573 2775165184341617597379295)
      ·
        refine ⟨4162747776512426396068943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775165184341617597379295 4162747776512426396068943)
        ·
          refine ⟨6244121664768639594103415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4162747776512426396068943 6244121664768639594103415)
          ·
            refine ⟨9366182497152959391155123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6244121664768639594103415 9366182497152959391155123)
            ·
              refine ⟨14049273745729439086732685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9366182497152959391155123 14049273745729439086732685)
              ·
                refine ⟨5268477654648539657524757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14049273745729439086732685 5268477654648539657524757)
                ·
                  refine ⟨246959890061650296446473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5268477654648539657524757 246959890061650296446473)
                  ·
                    rfl

theorem cell23_4328574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_4328574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328574 prefixEnd_4328574 := by exact prefixLift 4328574
  have htrace : WordTrace (prefixWord ++ tailWord_4328574) baseStart_4328574 baseEnd_4328574 := by
    simpa [prefixWord, tailWord_4328574, baseEnd_4328574] using wordTrace_append hprefix tailTrace_4328574
  have hstable : (prefixWord ++ tailWord_4328574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328574).length < 2 ^ (prefixWord ++ tailWord_4328574).sum := by decide
  have hdescent : baseEnd_4328574 < baseStart_4328574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328590 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4328590 : Nat := 118140960795 + 4328590 * 2 ^ 59
def prefixEnd_4328590 : Nat := 4983230072969 + 3 ^ 40 * 4328590 * 2
def baseEnd_4328590 : Nat := 2222647226245324605418183

theorem tailTrace_4328590 : CollatzResearch.WordTrace tailWord_4328590 prefixEnd_4328590 2222647226245324605418183 := by
  unfold tailWord_4328590
  simp only [CollatzResearch.WordTrace]
  refine ⟨19734580923533146145158903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105251098258843446107514149 19734580923533146145158903)
  ·
    refine ⟨29601871385299719217738355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19734580923533146145158903 29601871385299719217738355)
    ·
      refine ⟨44402807077949578826607533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29601871385299719217738355 44402807077949578826607533)
      ·
        refine ⟨16651052654231092059977825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44402807077949578826607533 16651052654231092059977825)
        ·
          refine ⟨12488289490673319044983369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16651052654231092059977825 12488289490673319044983369)
          ·
            refine ⟨9366217118004989283737527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12488289490673319044983369 9366217118004989283737527)
            ·
              refine ⟨14049325677007483925606291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9366217118004989283737527 14049325677007483925606291)
              ·
                refine ⟨21073988515511225888409437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14049325677007483925606291 21073988515511225888409437)
                ·
                  refine ⟨7902745693316709708153539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21073988515511225888409437 7902745693316709708153539)
                  ·
                    refine ⟨11854118539975064562230309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7902745693316709708153539 11854118539975064562230309)
                    ·
                      refine ⟨2222647226245324605418183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11854118539975064562230309 2222647226245324605418183)
                      ·
                        rfl

theorem cell23_4328590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4328590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328590 prefixEnd_4328590 := by exact prefixLift 4328590
  have htrace : WordTrace (prefixWord ++ tailWord_4328590) baseStart_4328590 baseEnd_4328590 := by
    simpa [prefixWord, tailWord_4328590, baseEnd_4328590] using wordTrace_append hprefix tailTrace_4328590
  have hstable : (prefixWord ++ tailWord_4328590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328590).length < 2 ^ (prefixWord ++ tailWord_4328590).sum := by decide
  have hdescent : baseEnd_4328590 < baseStart_4328590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328618 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4328618 : Nat := 118140960795 + 4328618 * 2 ^ 59
def prefixEnd_4328618 : Nat := 4983230072969 + 3 ^ 40 * 4328618 * 2
def baseEnd_4328618 : Nat := 2222661603703650495868055

theorem tailTrace_4328618 : CollatzResearch.WordTrace tailWord_4328618 prefixEnd_4328618 2222661603703650495868055 := by
  unfold tailWord_4328618
  simp only [CollatzResearch.WordTrace]
  refine ⟨39469417158040932485822627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105251779088109153295527005 39469417158040932485822627)
  ·
    refine ⟨59204125737061398728733941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39469417158040932485822627 59204125737061398728733941)
    ·
      refine ⟨5550386787849506130818807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59204125737061398728733941 5550386787849506130818807)
      ·
        refine ⟨8325580181774259196228211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5550386787849506130818807 8325580181774259196228211)
        ·
          refine ⟨12488370272661388794342317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8325580181774259196228211 12488370272661388794342317)
          ·
            refine ⟨4683138852248020797878369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12488370272661388794342317 4683138852248020797878369)
            ·
              refine ⟨3512354139186015598408777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4683138852248020797878369 3512354139186015598408777)
              ·
                refine ⟨2634265604389511698806583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3512354139186015598408777 2634265604389511698806583)
                ·
                  refine ⟨3951398406584267548209875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634265604389511698806583 3951398406584267548209875)
                  ·
                    refine ⟨5927097609876401322314813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3951398406584267548209875 5927097609876401322314813)
                    ·
                      refine ⟨2222661603703650495868055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5927097609876401322314813 2222661603703650495868055)
                      ·
                        rfl

theorem cell23_4328618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4328618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328618 prefixEnd_4328618 := by exact prefixLift 4328618
  have htrace : WordTrace (prefixWord ++ tailWord_4328618) baseStart_4328618 baseEnd_4328618 := by
    simpa [prefixWord, tailWord_4328618, baseEnd_4328618] using wordTrace_append hprefix tailTrace_4328618
  have hstable : (prefixWord ++ tailWord_4328618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328618).length < 2 ^ (prefixWord ++ tailWord_4328618).sum := by decide
  have hdescent : baseEnd_4328618 < baseStart_4328618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328673 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_4328673 : Nat := 118140960795 + 4328673 * 2 ^ 59
def prefixEnd_4328673 : Nat := 4983230072969 + 3 ^ 40 * 4328673 * 2
def baseEnd_4328673 : Nat := 740896615046549260226767

theorem tailTrace_4328673 : CollatzResearch.WordTrace tailWord_4328673 prefixEnd_4328673 740896615046549260226767 := by
  unfold tailWord_4328673
  simp only [CollatzResearch.WordTrace]
  refine ⟨157879674646964474336542673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105253116431309649557695115 157879674646964474336542673)
  ·
    refine ⟨118409755985223355752407005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157879674646964474336542673 118409755985223355752407005)
    ·
      refine ⟨44403658494458758407152627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118409755985223355752407005 44403658494458758407152627)
      ·
        refine ⟨66605487741688137610728941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44403658494458758407152627 66605487741688137610728941)
        ·
          refine ⟨24977057903133051604023353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66605487741688137610728941 24977057903133051604023353)
          ·
            refine ⟨18732793427349788703017515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24977057903133051604023353 18732793427349788703017515)
            ·
              refine ⟨28099190141024683054526273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18732793427349788703017515 28099190141024683054526273)
              ·
                refine ⟨21074392605768512290894705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28099190141024683054526273 21074392605768512290894705)
                ·
                  refine ⟨15805794454326384218171029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21074392605768512290894705 15805794454326384218171029)
                  ·
                    refine ⟨740896615046549260226767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15805794454326384218171029 740896615046549260226767)
                    ·
                      rfl

theorem cell23_4328673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_4328673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328673 prefixEnd_4328673 := by exact prefixLift 4328673
  have htrace : WordTrace (prefixWord ++ tailWord_4328673) baseStart_4328673 baseEnd_4328673 := by
    simpa [prefixWord, tailWord_4328673, baseEnd_4328673] using wordTrace_append hprefix tailTrace_4328673
  have hstable : (prefixWord ++ tailWord_4328673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328673).length < 2 ^ (prefixWord ++ tailWord_4328673).sum := by decide
  have hdescent : baseEnd_4328673 < baseStart_4328673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328703 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 7]
def baseStart_4328703 : Nat := 118140960795 + 4328703 * 2 ^ 59
def prefixEnd_4328703 : Nat := 4983230072969 + 3 ^ 40 * 4328703 * 2
def baseEnd_4328703 : Nat := 246967249951031407033907

theorem tailTrace_4328703 : CollatzResearch.WordTrace tailWord_4328703 prefixEnd_4328703 246967249951031407033907 := by
  unfold tailWord_4328703
  simp only [CollatzResearch.WordTrace]
  refine ⟨157880768836855789460134763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105253845891237192973423175 157880768836855789460134763)
  ·
    refine ⟨236821153255283684190202145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157880768836855789460134763 236821153255283684190202145)
    ·
      refine ⟨177615864941462763142651609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236821153255283684190202145 177615864941462763142651609)
      ·
        refine ⟨133211898706097072356988707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177615864941462763142651609 133211898706097072356988707)
        ·
          refine ⟨199817848059145608535483061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133211898706097072356988707 199817848059145608535483061)
          ·
            refine ⟨18732923255544900800201537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 199817848059145608535483061 18732923255544900800201537)
            ·
              refine ⟨14049692441658675600151153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18732923255544900800201537 14049692441658675600151153)
              ·
                refine ⟨10537269331244006700113365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14049692441658675600151153 10537269331244006700113365)
                ·
                  refine ⟨246967249951031407033907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10537269331244006700113365 246967249951031407033907)
                  ·
                    rfl

theorem cell23_4328703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 7].length) (baseStart_4328703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328703 prefixEnd_4328703 := by exact prefixLift 4328703
  have htrace : WordTrace (prefixWord ++ tailWord_4328703) baseStart_4328703 baseEnd_4328703 := by
    simpa [prefixWord, tailWord_4328703, baseEnd_4328703] using wordTrace_append hprefix tailTrace_4328703
  have hstable : (prefixWord ++ tailWord_4328703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328703).length < 2 ^ (prefixWord ++ tailWord_4328703).sum := by decide
  have hdescent : baseEnd_4328703 < baseStart_4328703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328783 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_4328783 : Nat := 118140960795 + 4328783 * 2 ^ 59
def prefixEnd_4328783 : Nat := 4983230072969 + 3 ^ 40 * 4328783 * 2
def baseEnd_4328783 : Nat := 2222746328011642350304795

theorem tailTrace_4328783 : CollatzResearch.WordTrace tailWord_4328783 prefixEnd_4328783 2222746328011642350304795 := by
  unfold tailWord_4328783
  simp only [CollatzResearch.WordTrace]
  refine ⟨157883686676565963123047003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105255791117710642082031335 157883686676565963123047003)
  ·
    refine ⟨236825530014848944684570505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157883686676565963123047003 236825530014848944684570505)
    ·
      refine ⟨177619147511136708513427879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236825530014848944684570505 177619147511136708513427879)
      ·
        refine ⟨266428721266705062770141819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177619147511136708513427879 266428721266705062770141819)
        ·
          refine ⟨399643081900057594155212729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266428721266705062770141819 399643081900057594155212729)
          ·
            refine ⟨299732311425043195616409547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399643081900057594155212729 299732311425043195616409547)
            ·
              refine ⟨449598467137564793424614321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299732311425043195616409547 449598467137564793424614321)
              ·
                refine ⟨337198850353173595068460741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449598467137564793424614321 337198850353173595068460741)
                ·
                  refine ⟨63224784441220049075336389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337198850353173595068460741 63224784441220049075336389)
                  ·
                    refine ⟨11854647082728759201625573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63224784441220049075336389 11854647082728759201625573)
                    ·
                      refine ⟨2222746328011642350304795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11854647082728759201625573 2222746328011642350304795)
                      ·
                        rfl

theorem cell23_4328783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_4328783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328783 prefixEnd_4328783 := by exact prefixLift 4328783
  have htrace : WordTrace (prefixWord ++ tailWord_4328783) baseStart_4328783 baseEnd_4328783 := by
    simpa [prefixWord, tailWord_4328783, baseEnd_4328783] using wordTrace_append hprefix tailTrace_4328783
  have hstable : (prefixWord ++ tailWord_4328783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328783).length < 2 ^ (prefixWord ++ tailWord_4328783).sum := by decide
  have hdescent : baseEnd_4328783 < baseStart_4328783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328793 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 8]
def baseStart_4328793 : Nat := 118140960795 + 4328793 * 2 ^ 59
def prefixEnd_4328793 : Nat := 4983230072969 + 3 ^ 40 * 4328793 * 2
def baseEnd_4328793 : Nat := 246972384757576367908861

theorem tailTrace_4328793 : CollatzResearch.WordTrace tailWord_4328793 prefixEnd_4328793 246972384757576367908861 := by
  unfold tailWord_4328793
  simp only [CollatzResearch.WordTrace]
  refine ⟨157884051406529734830911033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105256034271019823220607355 157884051406529734830911033)
  ·
    refine ⟨118413038554897301123183275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157884051406529734830911033 118413038554897301123183275)
    ·
      refine ⟨177619557832345951684774913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118413038554897301123183275 177619557832345951684774913)
      ·
        refine ⟨133214668374259463763581185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177619557832345951684774913 133214668374259463763581185)
        ·
          refine ⟨99911001280694597822685889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133214668374259463763581185 99911001280694597822685889)
          ·
            refine ⟨74933250960520948367014417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99911001280694597822685889 74933250960520948367014417)
            ·
              refine ⟨56199938220390711275260813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74933250960520948367014417 56199938220390711275260813)
              ·
                refine ⟨21074976832646516728222805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56199938220390711275260813 21074976832646516728222805)
                ·
                  refine ⟨246972384757576367908861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21074976832646516728222805 246972384757576367908861)
                  ·
                    rfl

theorem cell23_4328793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_4328793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328793 prefixEnd_4328793 := by exact prefixLift 4328793
  have htrace : WordTrace (prefixWord ++ tailWord_4328793) baseStart_4328793 baseEnd_4328793 := by
    simpa [prefixWord, tailWord_4328793, baseEnd_4328793] using wordTrace_append hprefix tailTrace_4328793
  have hstable : (prefixWord ++ tailWord_4328793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328793).length < 2 ^ (prefixWord ++ tailWord_4328793).sum := by decide
  have hdescent : baseEnd_4328793 < baseStart_4328793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328821 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4328821 : Nat := 118140960795 + 4328821 * 2 ^ 59
def prefixEnd_4328821 : Nat := 4983230072969 + 3 ^ 40 * 4328821 * 2
def baseEnd_4328821 : Nat := 2222765840276513201629621

theorem tailTrace_4328821 : CollatzResearch.WordTrace tailWord_4328821 prefixEnd_4328821 2222765840276513201629621 := by
  unfold tailWord_4328821
  simp only [CollatzResearch.WordTrace]
  refine ⟨157885072650428295612930317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105256715100285530408620211 157885072650428295612930317)
  ·
    refine ⟨59206902243910610854848869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157885072650428295612930317 59206902243910610854848869)
    ·
      refine ⟨11101294170733239535284163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59206902243910610854848869 11101294170733239535284163)
      ·
        refine ⟨16651941256099859302926245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11101294170733239535284163 16651941256099859302926245)
        ·
          refine ⟨3122238985518723619298671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16651941256099859302926245 3122238985518723619298671)
          ·
            refine ⟨4683358478278085428948007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122238985518723619298671 4683358478278085428948007)
            ·
              refine ⟨7025037717417128143422011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4683358478278085428948007 7025037717417128143422011)
              ·
                refine ⟨10537556576125692215133017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7025037717417128143422011 10537556576125692215133017)
                ·
                  refine ⟨7903167432094269161349763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10537556576125692215133017 7903167432094269161349763)
                  ·
                    refine ⟨11854751148141403742024645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7903167432094269161349763 11854751148141403742024645)
                    ·
                      refine ⟨2222765840276513201629621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11854751148141403742024645 2222765840276513201629621)
                      ·
                        rfl

theorem cell23_4328821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4328821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328821 prefixEnd_4328821 := by exact prefixLift 4328821
  have htrace : WordTrace (prefixWord ++ tailWord_4328821) baseStart_4328821 baseEnd_4328821 := by
    simpa [prefixWord, tailWord_4328821, baseEnd_4328821] using wordTrace_append hprefix tailTrace_4328821
  have hstable : (prefixWord ++ tailWord_4328821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328821).length < 2 ^ (prefixWord ++ tailWord_4328821).sum := by decide
  have hdescent : baseEnd_4328821 < baseStart_4328821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328911 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 1, 2, 2]
def baseStart_4328911 : Nat := 118140960795 + 4328911 * 2 ^ 59
def prefixEnd_4328911 : Nat := 4983230072969 + 3 ^ 40 * 4328911 * 2
def baseEnd_4328911 : Nat := 2222812053535417849504207

theorem tailTrace_4328911 : CollatzResearch.WordTrace tailWord_4328911 prefixEnd_4328911 2222812053535417849504207 := by
  unfold tailWord_4328911
  simp only [CollatzResearch.WordTrace]
  refine ⟨157888355220102240983706587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105258903480068160655804391 157888355220102240983706587)
  ·
    refine ⟨236832532830153361475559881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157888355220102240983706587 236832532830153361475559881)
    ·
      refine ⟨177624399622615021106669911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236832532830153361475559881 177624399622615021106669911)
      ·
        refine ⟨266436599433922531660004867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177624399622615021106669911 266436599433922531660004867)
        ·
          refine ⟨399654899150883797490007301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266436599433922531660004867 399654899150883797490007301)
          ·
            refine ⟨74935293590790712029376369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399654899150883797490007301 74935293590790712029376369)
            ·
              refine ⟨56201470193093034022032277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74935293590790712029376369 56201470193093034022032277)
              ·
                refine ⟨2634443915301235969782763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56201470193093034022032277 2634443915301235969782763)
                ·
                  refine ⟨3951665872951853954674145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634443915301235969782763 3951665872951853954674145)
                  ·
                    refine ⟨2963749404713890466005609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3951665872951853954674145 2963749404713890466005609)
                    ·
                      refine ⟨2222812053535417849504207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963749404713890466005609 2222812053535417849504207)
                      ·
                        rfl

theorem cell23_4328911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 1, 2, 2].length) (baseStart_4328911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328911 prefixEnd_4328911 := by exact prefixLift 4328911
  have htrace : WordTrace (prefixWord ++ tailWord_4328911) baseStart_4328911 baseEnd_4328911 := by
    simpa [prefixWord, tailWord_4328911, baseEnd_4328911] using wordTrace_append hprefix tailTrace_4328911
  have hstable : (prefixWord ++ tailWord_4328911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328911).length < 2 ^ (prefixWord ++ tailWord_4328911).sum := by decide
  have hdescent : baseEnd_4328911 < baseStart_4328911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328921 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 2, 4]
def baseStart_4328921 : Nat := 118140960795 + 4328921 * 2 ^ 59
def prefixEnd_4328921 : Nat := 4983230072969 + 3 ^ 40 * 4328921 * 2
def baseEnd_4328921 : Nat := 740939062780654270126387

theorem tailTrace_4328921 : CollatzResearch.WordTrace tailWord_4328921 prefixEnd_4328921 740939062780654270126387 := by
  unfold tailWord_4328921
  simp only [CollatzResearch.WordTrace]
  refine ⟨157888719950066012691570617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105259146633377341794380411 157888719950066012691570617)
  ·
    refine ⟨118416539962549509518677963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157888719950066012691570617 118416539962549509518677963)
    ·
      refine ⟨177624809943824264278016945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118416539962549509518677963 177624809943824264278016945)
      ·
        refine ⟨133218607457868198208512709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177624809943824264278016945 133218607457868198208512709)
        ·
          refine ⟨24978488898350287164096133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133218607457868198208512709 24978488898350287164096133)
          ·
            refine ⟨4683466668440678843268025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24978488898350287164096133 4683466668440678843268025)
            ·
              refine ⟨3512600001330509132451019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4683466668440678843268025 3512600001330509132451019)
              ·
                refine ⟨5268900001995763698676529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512600001330509132451019 5268900001995763698676529)
                ·
                  refine ⟨3951675001496822774007397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5268900001995763698676529 3951675001496822774007397)
                  ·
                    refine ⟨740939062780654270126387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3951675001496822774007397 740939062780654270126387)
                    ·
                      rfl

theorem cell23_4328921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 4].length) (baseStart_4328921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328921 prefixEnd_4328921 := by exact prefixLift 4328921
  have htrace : WordTrace (prefixWord ++ tailWord_4328921) baseStart_4328921 baseEnd_4328921 := by
    simpa [prefixWord, tailWord_4328921, baseEnd_4328921] using wordTrace_append hprefix tailTrace_4328921
  have hstable : (prefixWord ++ tailWord_4328921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328921).length < 2 ^ (prefixWord ++ tailWord_4328921).sum := by decide
  have hdescent : baseEnd_4328921 < baseStart_4328921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328927 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_4328927 : Nat := 118140960795 + 4328927 * 2 ^ 59
def prefixEnd_4328927 : Nat := 4983230072969 + 3 ^ 40 * 4328927 * 2
def baseEnd_4328927 : Nat := 2222820269225889786904133

theorem tailTrace_4328927 : CollatzResearch.WordTrace tailWord_4328927 prefixEnd_4328927 2222820269225889786904133 := by
  unfold tailWord_4328927
  simp only [CollatzResearch.WordTrace]
  refine ⟨157888938788044275716289035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105259292525362850477526023 157888938788044275716289035)
  ·
    refine ⟨236833408182066413574433553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157888938788044275716289035 236833408182066413574433553)
    ·
      refine ⟨177625056136549810180825165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236833408182066413574433553 177625056136549810180825165)
      ·
        refine ⟨66609396051206178817809437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177625056136549810180825165 66609396051206178817809437)
        ·
          refine ⟨24978523519202317056678539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66609396051206178817809437 24978523519202317056678539)
          ·
            refine ⟨37467785278803475585017809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24978523519202317056678539 37467785278803475585017809)
            ·
              refine ⟨28100838959102606688763357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37467785278803475585017809 28100838959102606688763357)
              ·
                refine ⟨10537814609663477508286259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28100838959102606688763357 10537814609663477508286259)
                ·
                  refine ⟨15806721914495216262429389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10537814609663477508286259 15806721914495216262429389)
                  ·
                    refine ⟨5927520717935706098411021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15806721914495216262429389 5927520717935706098411021)
                    ·
                      refine ⟨2222820269225889786904133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5927520717935706098411021 2222820269225889786904133)
                      ·
                        rfl

theorem cell23_4328927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_4328927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328927 prefixEnd_4328927 := by exact prefixLift 4328927
  have htrace : WordTrace (prefixWord ++ tailWord_4328927) baseStart_4328927 baseEnd_4328927 := by
    simpa [prefixWord, tailWord_4328927, baseEnd_4328927] using wordTrace_append hprefix tailTrace_4328927
  have hstable : (prefixWord ++ tailWord_4328927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328927).length < 2 ^ (prefixWord ++ tailWord_4328927).sum := by decide
  have hdescent : baseEnd_4328927 < baseStart_4328927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328931 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 3]
def baseStart_4328931 : Nat := 118140960795 + 4328931 * 2 ^ 59
def prefixEnd_4328931 : Nat := 4983230072969 + 3 ^ 40 * 4328931 * 2
def baseEnd_4328931 : Nat := 2222822323148507771254115

theorem tailTrace_4328931 : CollatzResearch.WordTrace tailWord_4328931 prefixEnd_4328931 2222822323148507771254115 := by
  unfold tailWord_4328931
  simp only [CollatzResearch.WordTrace]
  refine ⟨157889084680029784399434647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105259389786686522932956431 157889084680029784399434647)
  ·
    refine ⟨236833627020044676599151971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157889084680029784399434647 236833627020044676599151971)
    ·
      refine ⟨355250440530067014898727957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236833627020044676599151971 355250440530067014898727957)
      ·
        refine ⟨16652364399846891323377873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 355250440530067014898727957 16652364399846891323377873)
        ·
          refine ⟨12489273299885168492533405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16652364399846891323377873 12489273299885168492533405)
          ·
            refine ⟨4683477487456938184700027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12489273299885168492533405 4683477487456938184700027)
            ·
              refine ⟨7025216231185407277050041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4683477487456938184700027 7025216231185407277050041)
              ·
                refine ⟨5268912173389055457787531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7025216231185407277050041 5268912173389055457787531)
                ·
                  refine ⟨7903368260083583186681297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5268912173389055457787531 7903368260083583186681297)
                  ·
                    refine ⟨5927526195062687390010973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7903368260083583186681297 5927526195062687390010973)
                    ·
                      refine ⟨2222822323148507771254115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5927526195062687390010973 2222822323148507771254115)
                      ·
                        rfl

theorem cell23_4328931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_4328931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328931 prefixEnd_4328931 := by exact prefixLift 4328931
  have htrace : WordTrace (prefixWord ++ tailWord_4328931) baseStart_4328931 baseEnd_4328931 := by
    simpa [prefixWord, tailWord_4328931, baseEnd_4328931] using wordTrace_append hprefix tailTrace_4328931
  have hstable : (prefixWord ++ tailWord_4328931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328931).length < 2 ^ (prefixWord ++ tailWord_4328931).sum := by decide
  have hdescent : baseEnd_4328931 < baseStart_4328931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328940 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_4328940 : Nat := 118140960795 + 4328940 * 2 ^ 59
def prefixEnd_4328940 : Nat := 4983230072969 + 3 ^ 40 * 4328940 * 2
def baseEnd_4328940 : Nat := 2222826944474398236041573

theorem tailTrace_4328940 : CollatzResearch.WordTrace tailWord_4328940 prefixEnd_4328940 2222826944474398236041573 := by
  unfold tailWord_4328940
  simp only [CollatzResearch.WordTrace]
  refine ⟨78944706468498589468256137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105259608624664785957674849 78944706468498589468256137)
  ·
    refine ⟨59208529851373942101192103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78944706468498589468256137 59208529851373942101192103)
    ·
      refine ⟨88812794777060913151788155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59208529851373942101192103 88812794777060913151788155)
      ·
        refine ⟨133219192165591369727682233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88812794777060913151788155 133219192165591369727682233)
        ·
          refine ⟨99914394124193527295761675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133219192165591369727682233 99914394124193527295761675)
          ·
            refine ⟨149871591186290290943642513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99914394124193527295761675 149871591186290290943642513)
            ·
              refine ⟨112403693389717718207731885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149871591186290290943642513 112403693389717718207731885)
              ·
                refine ⟨42151385021144144327899457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112403693389717718207731885 42151385021144144327899457)
                ·
                  refine ⟨31613538765858108245924593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42151385021144144327899457 31613538765858108245924593)
                  ·
                    refine ⟨23710154074393581184443445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31613538765858108245924593 23710154074393581184443445)
                    ·
                      refine ⟨2222826944474398236041573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23710154074393581184443445 2222826944474398236041573)
                      ·
                        rfl

theorem cell23_4328940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_4328940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328940 prefixEnd_4328940 := by exact prefixLift 4328940
  have htrace : WordTrace (prefixWord ++ tailWord_4328940) baseStart_4328940 baseEnd_4328940 := by
    simpa [prefixWord, tailWord_4328940, baseEnd_4328940] using wordTrace_append hprefix tailTrace_4328940
  have hstable : (prefixWord ++ tailWord_4328940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328940).length < 2 ^ (prefixWord ++ tailWord_4328940).sum := by decide
  have hdescent : baseEnd_4328940 < baseStart_4328940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328962 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4328962 : Nat := 118140960795 + 4328962 * 2 ^ 59
def prefixEnd_4328962 : Nat := 4983230072969 + 3 ^ 40 * 4328962 * 2
def baseEnd_4328962 : Nat := 2222838241048797149966473

theorem tailTrace_4328962 : CollatzResearch.WordTrace tailWord_4328962 prefixEnd_4328962 2222838241048797149966473 := by
  unfold tailWord_4328962
  simp only [CollatzResearch.WordTrace]
  refine ⟨39472553835729369173453285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105260143561944984462542093 39472553835729369173453285)
  ·
    refine ⟨7401103844199256720022491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39472553835729369173453285 7401103844199256720022491)
    ·
      refine ⟨11101655766298885080033737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7401103844199256720022491 11101655766298885080033737)
      ·
        refine ⟨8326241824724163810025303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11101655766298885080033737 8326241824724163810025303)
        ·
          refine ⟨12489362737086245715037955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8326241824724163810025303 12489362737086245715037955)
          ·
            refine ⟨18734044105629368572556933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12489362737086245715037955 18734044105629368572556933)
            ·
              refine ⟨3512633269805506607354425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18734044105629368572556933 3512633269805506607354425)
              ·
                refine ⟨2634474952354129955515819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3512633269805506607354425 2634474952354129955515819)
                ·
                  refine ⟨3951712428531194933273729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634474952354129955515819 3951712428531194933273729)
                  ·
                    refine ⟨2963784321398396199955297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3951712428531194933273729 2963784321398396199955297)
                    ·
                      refine ⟨2222838241048797149966473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2963784321398396199955297 2222838241048797149966473)
                      ·
                        rfl

theorem cell23_4328962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4328962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328962 prefixEnd_4328962 := by exact prefixLift 4328962
  have htrace : WordTrace (prefixWord ++ tailWord_4328962) baseStart_4328962 baseEnd_4328962 := by
    simpa [prefixWord, tailWord_4328962, baseEnd_4328962] using wordTrace_append hprefix tailTrace_4328962
  have hstable : (prefixWord ++ tailWord_4328962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328962).length < 2 ^ (prefixWord ++ tailWord_4328962).sum := by decide
  have hdescent : baseEnd_4328962 < baseStart_4328962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4328967 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4328967 : Nat := 118140960795 + 4328967 * 2 ^ 59
def prefixEnd_4328967 : Nat := 4983230072969 + 3 ^ 40 * 4328967 * 2
def baseEnd_4328967 : Nat := 2222840808452069630403949

theorem tailTrace_4328967 : CollatzResearch.WordTrace tailWord_4328967 prefixEnd_4328967 2222840808452069630403949 := by
  unfold tailWord_4328967
  simp only [CollatzResearch.WordTrace]
  refine ⟨157890397707899362547745155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105260265138599575031830103 157890397707899362547745155)
  ·
    refine ⟨236835596561849043821617733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157890397707899362547745155 236835596561849043821617733)
    ·
      refine ⟨44406674355346695716553325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236835596561849043821617733 44406674355346695716553325)
      ·
        refine ⟨16652502883255010893707497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44406674355346695716553325 16652502883255010893707497)
        ·
          refine ⟨12489377162441258170280623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16652502883255010893707497 12489377162441258170280623)
          ·
            refine ⟨18734065743661887255420935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12489377162441258170280623 18734065743661887255420935)
            ·
              refine ⟨28101098615492830883131403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18734065743661887255420935 28101098615492830883131403)
              ·
                refine ⟨42151647923239246324697105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28101098615492830883131403 42151647923239246324697105)
                ·
                  refine ⟨31613735942429434743522829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42151647923239246324697105 31613735942429434743522829)
                  ·
                    refine ⟨11855150978411038028821061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31613735942429434743522829 11855150978411038028821061)
                    ·
                      refine ⟨2222840808452069630403949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11855150978411038028821061 2222840808452069630403949)
                      ·
                        rfl

theorem cell23_4328967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4328967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4328967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4328967 prefixEnd_4328967 := by exact prefixLift 4328967
  have htrace : WordTrace (prefixWord ++ tailWord_4328967) baseStart_4328967 baseEnd_4328967 := by
    simpa [prefixWord, tailWord_4328967, baseEnd_4328967] using wordTrace_append hprefix tailTrace_4328967
  have hstable : (prefixWord ++ tailWord_4328967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4328967).length < 2 ^ (prefixWord ++ tailWord_4328967).sum := by decide
  have hdescent : baseEnd_4328967 < baseStart_4328967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4328967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329057 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_4329057 : Nat := 118140960795 + 4329057 * 2 ^ 59
def prefixEnd_4329057 : Nat := 4983230072969 + 3 ^ 40 * 4329057 * 2
def baseEnd_4329057 : Nat := 2222887021710974278278535

theorem tailTrace_4329057 : CollatzResearch.WordTrace tailWord_4329057 prefixEnd_4329057 2222887021710974278278535 := by
  unfold tailWord_4329057
  simp only [CollatzResearch.WordTrace]
  refine ⟨157893680277573307918521425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105262453518382205279014283 157893680277573307918521425)
  ·
    refine ⟨118420260208179980938891069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157893680277573307918521425 118420260208179980938891069)
    ·
      refine ⟨44407597578067492852084151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118420260208179980938891069 44407597578067492852084151)
      ·
        refine ⟨66611396367101239278126227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44407597578067492852084151 66611396367101239278126227)
        ·
          refine ⟨99917094550651858917189341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66611396367101239278126227 99917094550651858917189341)
          ·
            refine ⟨37468910456494447093946003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99917094550651858917189341 37468910456494447093946003)
            ·
              refine ⟨56203365684741670640919005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37468910456494447093946003 56203365684741670640919005)
              ·
                refine ⟨21076262131778126490344627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56203365684741670640919005 21076262131778126490344627)
                ·
                  refine ⟨31614393197667189735516941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21076262131778126490344627 31614393197667189735516941)
                  ·
                    refine ⟨11855397449125196150818853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31614393197667189735516941 11855397449125196150818853)
                    ·
                      refine ⟨2222887021710974278278535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11855397449125196150818853 2222887021710974278278535)
                      ·
                        rfl

theorem cell23_4329057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_4329057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329057 prefixEnd_4329057 := by exact prefixLift 4329057
  have htrace : WordTrace (prefixWord ++ tailWord_4329057) baseStart_4329057 baseEnd_4329057 := by
    simpa [prefixWord, tailWord_4329057, baseEnd_4329057] using wordTrace_append hprefix tailTrace_4329057
  have hstable : (prefixWord ++ tailWord_4329057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329057).length < 2 ^ (prefixWord ++ tailWord_4329057).sum := by decide
  have hdescent : baseEnd_4329057 < baseStart_4329057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329074 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4329074 : Nat := 118140960795 + 4329074 * 2 ^ 59
def prefixEnd_4329074 : Nat := 4983230072969 + 3 ^ 40 * 4329074 * 2
def baseEnd_4329074 : Nat := 2222895750882100711765957

theorem tailTrace_4329074 : CollatzResearch.WordTrace tailWord_4329074 prefixEnd_4329074 2222895750882100711765957 := by
  unfold tailWord_4329074
  simp only [CollatzResearch.WordTrace]
  refine ⟨39473575079627929955472569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105262866879007813214593517 39473575079627929955472569)
  ·
    refine ⟨29605181309720947466604427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39473575079627929955472569 29605181309720947466604427)
    ·
      refine ⟨44407771964581421199906641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29605181309720947466604427 44407771964581421199906641)
      ·
        refine ⟨33305828973436065899929981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44407771964581421199906641 33305828973436065899929981)
        ·
          refine ⟨12489685865038524712473743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33305828973436065899929981 12489685865038524712473743)
          ·
            refine ⟨18734528797557787068710615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12489685865038524712473743 18734528797557787068710615)
            ·
              refine ⟨28101793196336680603065923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18734528797557787068710615 28101793196336680603065923)
              ·
                refine ⟨42152689794505020904598885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28101793196336680603065923 42152689794505020904598885)
                ·
                  refine ⟨7903629336469691419612291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42152689794505020904598885 7903629336469691419612291)
                  ·
                    refine ⟨11855444004704537129418437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7903629336469691419612291 11855444004704537129418437)
                    ·
                      refine ⟨2222895750882100711765957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11855444004704537129418437 2222895750882100711765957)
                      ·
                        rfl

theorem cell23_4329074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4329074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329074 prefixEnd_4329074 := by exact prefixLift 4329074
  have htrace : WordTrace (prefixWord ++ tailWord_4329074) baseStart_4329074 baseEnd_4329074 := by
    simpa [prefixWord, tailWord_4329074, baseEnd_4329074] using wordTrace_append hprefix tailTrace_4329074
  have hstable : (prefixWord ++ tailWord_4329074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329074).length < 2 ^ (prefixWord ++ tailWord_4329074).sum := by decide
  have hdescent : baseEnd_4329074 < baseStart_4329074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329108 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4329108 : Nat := 118140960795 + 4329108 * 2 ^ 59
def prefixEnd_4329108 : Nat := 4983230072969 + 3 ^ 40 * 4329108 * 2
def baseEnd_4329108 : Nat := 2222913209224353578740801

theorem tailTrace_4329108 : CollatzResearch.WordTrace tailWord_4329108 prefixEnd_4329108 2222913209224353578740801 := by
  unfold tailWord_4329108
  simp only [CollatzResearch.WordTrace]
  refine ⟨78947770200194271814313989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105263693600259029085751985 78947770200194271814313989)
  ·
    refine ⟨14802706912536425965183873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78947770200194271814313989 14802706912536425965183873)
    ·
      refine ⟨11102030184402319473887905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14802706912536425965183873 11102030184402319473887905)
      ·
        refine ⟨8326522638301739605415929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11102030184402319473887905 8326522638301739605415929)
        ·
          refine ⟨6244891978726304704061947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8326522638301739605415929 6244891978726304704061947)
          ·
            refine ⟨9367337968089457056092921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6244891978726304704061947 9367337968089457056092921)
            ·
              refine ⟨7025503476067092792069691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9367337968089457056092921 7025503476067092792069691)
              ·
                refine ⟨10538255214100639188104537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7025503476067092792069691 10538255214100639188104537)
                ·
                  refine ⟨7903691410575479391078403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10538255214100639188104537 7903691410575479391078403)
                  ·
                    refine ⟨11855537115863219086617605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7903691410575479391078403 11855537115863219086617605)
                    ·
                      refine ⟨2222913209224353578740801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11855537115863219086617605 2222913209224353578740801)
                      ·
                        rfl

theorem cell23_4329108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4329108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329108 prefixEnd_4329108 := by exact prefixLift 4329108
  have htrace : WordTrace (prefixWord ++ tailWord_4329108) baseStart_4329108 baseEnd_4329108 := by
    simpa [prefixWord, tailWord_4329108, baseEnd_4329108] using wordTrace_append hprefix tailTrace_4329108
  have hstable : (prefixWord ++ tailWord_4329108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329108).length < 2 ^ (prefixWord ++ tailWord_4329108).sum := by decide
  have hdescent : baseEnd_4329108 < baseStart_4329108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329111 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_4329111 : Nat := 118140960795 + 4329111 * 2 ^ 59
def prefixEnd_4329111 : Nat := 4983230072969 + 3 ^ 40 * 4329111 * 2
def baseEnd_4329111 : Nat := 2222914749666317067003287

theorem tailTrace_4329111 : CollatzResearch.WordTrace tailWord_4329111 prefixEnd_4329111 2222914749666317067003287 := by
  unfold tailWord_4329111
  simp only [CollatzResearch.WordTrace]
  refine ⟨157895649819377675140987187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105263766546251783427324791 157895649819377675140987187)
  ·
    refine ⟨236843474729066512711480781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157895649819377675140987187 236843474729066512711480781)
    ·
      refine ⟨88816303023399942266805293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236843474729066512711480781 88816303023399942266805293)
      ·
        refine ⟨33306113633774978350051985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88816303023399942266805293 33306113633774978350051985)
        ·
          refine ⟨24979585225331233762538989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33306113633774978350051985 24979585225331233762538989)
          ·
            refine ⟨9367344459499212660952121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24979585225331233762538989 9367344459499212660952121)
            ·
              refine ⟨7025508344624409495714091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9367344459499212660952121 7025508344624409495714091)
              ·
                refine ⟨10538262516936614243571137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7025508344624409495714091 10538262516936614243571137)
                ·
                  refine ⟨7903696887702460682678353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10538262516936614243571137 7903696887702460682678353)
                  ·
                    refine ⟨5927772665776845512008765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7903696887702460682678353 5927772665776845512008765)
                    ·
                      refine ⟨2222914749666317067003287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5927772665776845512008765 2222914749666317067003287)
                      ·
                        rfl

theorem cell23_4329111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_4329111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329111 prefixEnd_4329111 := by exact prefixLift 4329111
  have htrace : WordTrace (prefixWord ++ tailWord_4329111) baseStart_4329111 baseEnd_4329111 := by
    simpa [prefixWord, tailWord_4329111, baseEnd_4329111] using wordTrace_append hprefix tailTrace_4329111
  have hstable : (prefixWord ++ tailWord_4329111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329111).length < 2 ^ (prefixWord ++ tailWord_4329111).sum := by decide
  have hdescent : baseEnd_4329111 < baseStart_4329111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329117 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4329117 : Nat := 118140960795 + 4329117 * 2 ^ 59
def prefixEnd_4329117 : Nat := 4983230072969 + 3 ^ 40 * 4329117 * 2
def baseEnd_4329117 : Nat := 2222917830550244043528259

theorem tailTrace_4329117 : CollatzResearch.WordTrace tailWord_4329117 prefixEnd_4329117 2222917830550244043528259 := by
  unfold tailWord_4329117
  simp only [CollatzResearch.WordTrace]
  refine ⟨157895868657355938165705605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105263912438237292110470403 157895868657355938165705605)
  ·
    refine ⟨29605475373254238406069801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157895868657355938165705605 29605475373254238406069801)
    ·
      refine ⟨22204106529940678804552351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29605475373254238406069801 22204106529940678804552351)
      ·
        refine ⟨33306159794911018206828527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22204106529940678804552351 33306159794911018206828527)
        ·
          refine ⟨49959239692366527310242791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33306159794911018206828527 49959239692366527310242791)
          ·
            refine ⟨74938859538549790965364187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49959239692366527310242791 74938859538549790965364187)
            ·
              refine ⟨112408289307824686448046281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74938859538549790965364187 112408289307824686448046281)
              ·
                refine ⟨84306216980868514836034711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112408289307824686448046281 84306216980868514836034711)
                ·
                  refine ⟨126459325471302772254052067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84306216980868514836034711 126459325471302772254052067)
                  ·
                    refine ⟨189688988206954158381078101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126459325471302772254052067 189688988206954158381078101)
                    ·
                      refine ⟨2222917830550244043528259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189688988206954158381078101 2222917830550244043528259)
                      ·
                        rfl

theorem cell23_4329117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4329117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329117 prefixEnd_4329117 := by exact prefixLift 4329117
  have htrace : WordTrace (prefixWord ++ tailWord_4329117) baseStart_4329117 baseEnd_4329117 := by
    simpa [prefixWord, tailWord_4329117, baseEnd_4329117] using wordTrace_append hprefix tailTrace_4329117
  have hstable : (prefixWord ++ tailWord_4329117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329117).length < 2 ^ (prefixWord ++ tailWord_4329117).sum := by decide
  have hdescent : baseEnd_4329117 < baseStart_4329117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329157 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_4329157 : Nat := 118140960795 + 4329157 * 2 ^ 59
def prefixEnd_4329157 : Nat := 4983230072969 + 3 ^ 40 * 4329157 * 2
def baseEnd_4329157 : Nat := 740979456592141295676025

theorem tailTrace_4329157 : CollatzResearch.WordTrace tailWord_4329157 prefixEnd_4329157 740979456592141295676025 := by
  unfold tailWord_4329157
  simp only [CollatzResearch.WordTrace]
  refine ⟨157897327577211024997161725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105264885051474016664774483 157897327577211024997161725)
  ·
    refine ⟨59211497841454134373935647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157897327577211024997161725 59211497841454134373935647)
    ·
      refine ⟨88817246762181201560903471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59211497841454134373935647 88817246762181201560903471)
      ·
        refine ⟨133225870143271802341355207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88817246762181201560903471 133225870143271802341355207)
        ·
          refine ⟨199838805214907703512032811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133225870143271802341355207 199838805214907703512032811)
          ·
            refine ⟨299758207822361555268049217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199838805214907703512032811 299758207822361555268049217)
            ·
              refine ⟨224818655866771166451036913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299758207822361555268049217 224818655866771166451036913)
              ·
                refine ⟨168613991900078374838277685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224818655866771166451036913 168613991900078374838277685)
                ·
                  refine ⟨15807561740632347641088533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168613991900078374838277685 15807561740632347641088533)
                  ·
                    refine ⟨740979456592141295676025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15807561740632347641088533 740979456592141295676025)
                    ·
                      rfl

theorem cell23_4329157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_4329157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329157 prefixEnd_4329157 := by exact prefixLift 4329157
  have htrace : WordTrace (prefixWord ++ tailWord_4329157) baseStart_4329157 baseEnd_4329157 := by
    simpa [prefixWord, tailWord_4329157, baseEnd_4329157] using wordTrace_append hprefix tailTrace_4329157
  have hstable : (prefixWord ++ tailWord_4329157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329157).length < 2 ^ (prefixWord ++ tailWord_4329157).sum := by decide
  have hdescent : baseEnd_4329157 < baseStart_4329157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329178 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_4329178 : Nat := 118140960795 + 4329178 * 2 ^ 59
def prefixEnd_4329178 : Nat := 4983230072969 + 3 ^ 40 * 4329178 * 2
def baseEnd_4329178 : Nat := 740983050956722768288493

theorem tailTrace_4329178 : CollatzResearch.WordTrace tailWord_4329178 prefixEnd_4329178 740983050956722768288493 := by
  unfold tailWord_4329178
  simp only [CollatzResearch.WordTrace]
  refine ⟨39474523377533736395919047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105265395673423297055784125 39474523377533736395919047)
  ·
    refine ⟨59211785066300604593878571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39474523377533736395919047 59211785066300604593878571)
    ·
      refine ⟨88817677599450906890817857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59211785066300604593878571 88817677599450906890817857)
      ·
        refine ⟨66613258199588180168113393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88817677599450906890817857 66613258199588180168113393)
        ·
          refine ⟨49959943649691135126085045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66613258199588180168113393 49959943649691135126085045)
          ·
            refine ⟨4683744717158543918070473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49959943649691135126085045 4683744717158543918070473)
            ·
              refine ⟨3512808537868907938552855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4683744717158543918070473 3512808537868907938552855)
              ·
                refine ⟨5269212806803361907829283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512808537868907938552855 5269212806803361907829283)
                ·
                  refine ⟨7903819210205042861743925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269212806803361907829283 7903819210205042861743925)
                  ·
                    refine ⟨740983050956722768288493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7903819210205042861743925 740983050956722768288493)
                    ·
                      rfl

theorem cell23_4329178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_4329178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329178 prefixEnd_4329178 := by exact prefixLift 4329178
  have htrace : WordTrace (prefixWord ++ tailWord_4329178) baseStart_4329178 baseEnd_4329178 := by
    simpa [prefixWord, tailWord_4329178, baseEnd_4329178] using wordTrace_append hprefix tailTrace_4329178
  have hstable : (prefixWord ++ tailWord_4329178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329178).length < 2 ^ (prefixWord ++ tailWord_4329178).sum := by decide
  have hdescent : baseEnd_4329178 < baseStart_4329178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329194 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_4329194 : Nat := 118140960795 + 4329194 * 2 ^ 59
def prefixEnd_4329194 : Nat := 4983230072969 + 3 ^ 40 * 4329194 * 2
def baseEnd_4329194 : Nat := 2222957368560640242265405

theorem tailTrace_4329194 : CollatzResearch.WordTrace tailWord_4329194 prefixEnd_4329194 2222957368560640242265405 := by
  unfold tailWord_4329194
  simp only [CollatzResearch.WordTrace]
  refine ⟨39474669269519245079064659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105265784718717986877505757 39474669269519245079064659)
  ·
    refine ⟨59212003904278867618596989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39474669269519245079064659 59212003904278867618596989)
    ·
      refine ⟨22204501464104575356973871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59212003904278867618596989 22204501464104575356973871)
      ·
        refine ⟨33306752196156863035460807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22204501464104575356973871 33306752196156863035460807)
        ·
          refine ⟨49960128294235294553191211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33306752196156863035460807 49960128294235294553191211)
          ·
            refine ⟨74940192441352941829786817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49960128294235294553191211 74940192441352941829786817)
            ·
              refine ⟨56205144331014706372340113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74940192441352941829786817 56205144331014706372340113)
              ·
                refine ⟨42153858248261029779255085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56205144331014706372340113 42153858248261029779255085)
                ·
                  refine ⟨15807696843097886167220657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42153858248261029779255085 15807696843097886167220657)
                  ·
                    refine ⟨11855772632323414625415493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15807696843097886167220657 11855772632323414625415493)
                    ·
                      refine ⟨2222957368560640242265405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11855772632323414625415493 2222957368560640242265405)
                      ·
                        rfl

theorem cell23_4329194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_4329194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329194 prefixEnd_4329194 := by exact prefixLift 4329194
  have htrace : WordTrace (prefixWord ++ tailWord_4329194) baseStart_4329194 baseEnd_4329194 := by
    simpa [prefixWord, tailWord_4329194, baseEnd_4329194] using wordTrace_append hprefix tailTrace_4329194
  have hstable : (prefixWord ++ tailWord_4329194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329194).length < 2 ^ (prefixWord ++ tailWord_4329194).sum := by decide
  have hdescent : baseEnd_4329194 < baseStart_4329194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329244 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4329244 : Nat := 118140960795 + 4329244 * 2 ^ 59
def prefixEnd_4329244 : Nat := 4983230072969 + 3 ^ 40 * 4329244 * 2
def baseEnd_4329244 : Nat := 2222983042593365046640175

theorem tailTrace_4329244 : CollatzResearch.WordTrace tailWord_4329244 prefixEnd_4329244 2222983042593365046640175 := by
  unfold tailWord_4329244
  simp only [CollatzResearch.WordTrace]
  refine ⟨78950250363947919427789393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105267000485263892570385857 78950250363947919427789393)
  ·
    refine ⟨59212687772960939570842045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78950250363947919427789393 59212687772960939570842045)
    ·
      refine ⟨22204757914860352339065767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59212687772960939570842045 22204757914860352339065767)
      ·
        refine ⟨33307136872290528508598651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22204757914860352339065767 33307136872290528508598651)
        ·
          refine ⟨49960705308435792762897977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33307136872290528508598651 49960705308435792762897977)
          ·
            refine ⟨37470528981326844572173483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49960705308435792762897977 37470528981326844572173483)
            ·
              refine ⟨56205793471990266858260225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37470528981326844572173483 56205793471990266858260225)
              ·
                refine ⟨42154345103992700143695169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56205793471990266858260225 42154345103992700143695169)
                ·
                  refine ⟨31615758827994525107771377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42154345103992700143695169 31615758827994525107771377)
                  ·
                    refine ⟨23711819120995893830828533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31615758827994525107771377 23711819120995893830828533)
                    ·
                      refine ⟨2222983042593365046640175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23711819120995893830828533 2222983042593365046640175)
                      ·
                        rfl

theorem cell23_4329244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4329244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329244 prefixEnd_4329244 := by exact prefixLift 4329244
  have htrace : WordTrace (prefixWord ++ tailWord_4329244) baseStart_4329244 baseEnd_4329244 := by
    simpa [prefixWord, tailWord_4329244, baseEnd_4329244] using wordTrace_append hprefix tailTrace_4329244
  have hstable : (prefixWord ++ tailWord_4329244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329244).length < 2 ^ (prefixWord ++ tailWord_4329244).sum := by decide
  have hdescent : baseEnd_4329244 < baseStart_4329244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329248 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4329248 : Nat := 118140960795 + 4329248 * 2 ^ 59
def prefixEnd_4329248 : Nat := 4983230072969 + 3 ^ 40 * 4329248 * 2
def baseEnd_4329248 : Nat := 2222985096515983030990157

theorem tailTrace_4329248 : CollatzResearch.WordTrace tailWord_4329248 prefixEnd_4329248 2222985096515983030990157 := by
  unfold tailWord_4329248
  simp only [CollatzResearch.WordTrace]
  refine ⟨78950323309940673769362199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105267097746587565025816265 78950323309940673769362199)
  ·
    refine ⟨118425484964911010654043299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78950323309940673769362199 118425484964911010654043299)
    ·
      refine ⟨177638227447366515981064949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118425484964911010654043299 177638227447366515981064949)
      ·
        refine ⟨16653583823190610873224839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177638227447366515981064949 16653583823190610873224839)
        ·
          refine ⟨24980375734785916309837259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16653583823190610873224839 24980375734785916309837259)
          ·
            refine ⟨37470563602178874464755889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24980375734785916309837259 37470563602178874464755889)
            ·
              refine ⟨28102922701634155848566917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37470563602178874464755889 28102922701634155848566917)
              ·
                refine ⟨5269298006556404221606297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28102922701634155848566917 5269298006556404221606297)
                ·
                  refine ⟨3951973504917303166204723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269298006556404221606297 3951973504917303166204723)
                  ·
                    refine ⟨5927960257375954749307085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3951973504917303166204723 5927960257375954749307085)
                    ·
                      refine ⟨2222985096515983030990157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5927960257375954749307085 2222985096515983030990157)
                      ·
                        rfl

theorem cell23_4329248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4329248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329248 prefixEnd_4329248 := by exact prefixLift 4329248
  have htrace : WordTrace (prefixWord ++ tailWord_4329248) baseStart_4329248 baseEnd_4329248 := by
    simpa [prefixWord, tailWord_4329248, baseEnd_4329248] using wordTrace_append hprefix tailTrace_4329248
  have hstable : (prefixWord ++ tailWord_4329248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329248).length < 2 ^ (prefixWord ++ tailWord_4329248).sum := by decide
  have hdescent : baseEnd_4329248 < baseStart_4329248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329265 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 2, 1, 3]
def baseStart_4329265 : Nat := 118140960795 + 4329265 * 2 ^ 59
def prefixEnd_4329265 : Nat := 4983230072969 + 3 ^ 40 * 4329265 * 2
def baseEnd_4329265 : Nat := 2222993825687109464477579

theorem tailTrace_4329265 : CollatzResearch.WordTrace tailWord_4329265 prefixEnd_4329265 2222993825687109464477579 := by
  unfold tailWord_4329265
  simp only [CollatzResearch.WordTrace]
  refine ⟨157901266660819759442093249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105267511107213172961395499 157901266660819759442093249)
  ·
    refine ⟨118425949995614819581569937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157901266660819759442093249 118425949995614819581569937)
    ·
      refine ⟨88819462496711114686177453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118425949995614819581569937 88819462496711114686177453)
      ·
        refine ⟨33307298436266668007316545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88819462496711114686177453 33307298436266668007316545)
        ·
          refine ⟨24980473827200001005487409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33307298436266668007316545 24980473827200001005487409)
          ·
            refine ⟨18735355370400000754115557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24980473827200001005487409 18735355370400000754115557)
            ·
              refine ⟨3512879131950000141396667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18735355370400000754115557 3512879131950000141396667)
              ·
                refine ⟨5269318697925000212095001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512879131950000141396667 5269318697925000212095001)
                ·
                  refine ⟨3951989023443750159071251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269318697925000212095001 3951989023443750159071251)
                  ·
                    refine ⟨5927983535165625238606877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3951989023443750159071251 5927983535165625238606877)
                    ·
                      refine ⟨2222993825687109464477579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5927983535165625238606877 2222993825687109464477579)
                      ·
                        rfl

theorem cell23_4329265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_4329265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329265 prefixEnd_4329265 := by exact prefixLift 4329265
  have htrace : WordTrace (prefixWord ++ tailWord_4329265) baseStart_4329265 baseEnd_4329265 := by
    simpa [prefixWord, tailWord_4329265, baseEnd_4329265] using wordTrace_append hprefix tailTrace_4329265
  have hstable : (prefixWord ++ tailWord_4329265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329265).length < 2 ^ (prefixWord ++ tailWord_4329265).sum := by decide
  have hdescent : baseEnd_4329265 < baseStart_4329265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329288 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_4329288 : Nat := 118140960795 + 4329288 * 2 ^ 59
def prefixEnd_4329288 : Nat := 4983230072969 + 3 ^ 40 * 4329288 * 2
def baseEnd_4329288 : Nat := 2223005635742162874489973

theorem tailTrace_4329288 : CollatzResearch.WordTrace tailWord_4329288 prefixEnd_4329288 2223005635742162874489973 := by
  unfold tailWord_4329288
  simp only [CollatzResearch.WordTrace]
  refine ⟨78951052769868217185090259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105268070359824289580120345 78951052769868217185090259)
  ·
    refine ⟨118426579154802325777635389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78951052769868217185090259 118426579154802325777635389)
    ·
      refine ⟨44409967183050872166613271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118426579154802325777635389 44409967183050872166613271)
      ·
        refine ⟨66614950774576308249919907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44409967183050872166613271 66614950774576308249919907)
        ·
          refine ⟨99922426161864462374879861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66614950774576308249919907 99922426161864462374879861)
          ·
            refine ⟨9367727452674793347644987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99922426161864462374879861 9367727452674793347644987)
            ·
              refine ⟨14051591179012190021467481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9367727452674793347644987 14051591179012190021467481)
              ·
                refine ⟨10538693384259142516100611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14051591179012190021467481 10538693384259142516100611)
                ·
                  refine ⟨15808040076388713774150917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10538693384259142516100611 15808040076388713774150917)
                  ·
                    refine ⟨2964007514322883832653297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15808040076388713774150917 2964007514322883832653297)
                    ·
                      refine ⟨2223005635742162874489973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964007514322883832653297 2223005635742162874489973)
                      ·
                        rfl

theorem cell23_4329288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_4329288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329288 prefixEnd_4329288 := by exact prefixLift 4329288
  have htrace : WordTrace (prefixWord ++ tailWord_4329288) baseStart_4329288 baseEnd_4329288 := by
    simpa [prefixWord, tailWord_4329288, baseEnd_4329288] using wordTrace_append hprefix tailTrace_4329288
  have hstable : (prefixWord ++ tailWord_4329288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329288).length < 2 ^ (prefixWord ++ tailWord_4329288).sum := by decide
  have hdescent : baseEnd_4329288 < baseStart_4329288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329292 : List Nat := [2, 2, 1, 3, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4329292 : Nat := 118140960795 + 4329292 * 2 ^ 59
def prefixEnd_4329292 : Nat := 4983230072969 + 3 ^ 40 * 4329292 * 2
def baseEnd_4329292 : Nat := 2223007689664780858839955

theorem tailTrace_4329292 : CollatzResearch.WordTrace tailWord_4329292 prefixEnd_4329292 2223007689664780858839955 := by
  unfold tailWord_4329292
  simp only [CollatzResearch.WordTrace]
  refine ⟨78951125715860971526663065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 105268167621147962035550753 78951125715860971526663065)
  ·
    refine ⟨59213344286895728644997299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78951125715860971526663065 59213344286895728644997299)
    ·
      refine ⟨88820016430343592967495949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59213344286895728644997299 88820016430343592967495949)
      ·
        refine ⟨33307506161378847362810981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88820016430343592967495949 33307506161378847362810981)
        ·
          refine ⟨6245157405258533880527059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33307506161378847362810981 6245157405258533880527059)
          ·
            refine ⟨9367736107887800820790589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6245157405258533880527059 9367736107887800820790589)
            ·
              refine ⟨3512901040457925307796471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9367736107887800820790589 3512901040457925307796471)
              ·
                refine ⟨5269351560686887961694707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512901040457925307796471 5269351560686887961694707)
                ·
                  refine ⟨7904027341030331942542061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5269351560686887961694707 7904027341030331942542061)
                  ·
                    refine ⟨2964010252886374478453273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7904027341030331942542061 2964010252886374478453273)
                    ·
                      refine ⟨2223007689664780858839955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964010252886374478453273 2223007689664780858839955)
                      ·
                        rfl

theorem cell23_4329292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4329292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329292 prefixEnd_4329292 := by exact prefixLift 4329292
  have htrace : WordTrace (prefixWord ++ tailWord_4329292) baseStart_4329292 baseEnd_4329292 := by
    simpa [prefixWord, tailWord_4329292, baseEnd_4329292] using wordTrace_append hprefix tailTrace_4329292
  have hstable : (prefixWord ++ tailWord_4329292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329292).length < 2 ^ (prefixWord ++ tailWord_4329292).sum := by decide
  have hdescent : baseEnd_4329292 < baseStart_4329292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329305 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 2, 2, 2]
def baseStart_4329305 : Nat := 118140960795 + 4329305 * 2 ^ 59
def prefixEnd_4329305 : Nat := 4983230072969 + 3 ^ 40 * 4329305 * 2
def baseEnd_4329305 : Nat := 2223014364913289307977395

theorem tailTrace_4329305 : CollatzResearch.WordTrace tailWord_4329305 prefixEnd_4329305 2223014364913289307977395 := by
  unfold tailWord_4329305
  simp only [CollatzResearch.WordTrace]
  refine ⟨157902725580674846273549369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105268483720449897515699579 157902725580674846273549369)
  ·
    refine ⟨118427044185506134705162027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157902725580674846273549369 118427044185506134705162027)
    ·
      refine ⟨177640566278259202057743041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118427044185506134705162027 177640566278259202057743041)
      ·
        refine ⟨133230424708694401543307281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177640566278259202057743041 133230424708694401543307281)
        ·
          refine ⟨99922818531520801157480461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133230424708694401543307281 99922818531520801157480461)
          ·
            refine ⟨37471056949320300434055173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99922818531520801157480461 37471056949320300434055173)
            ·
              refine ⟨7025823177997556331385345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37471056949320300434055173 7025823177997556331385345)
              ·
                refine ⟨5269367383498167248539009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7025823177997556331385345 5269367383498167248539009)
                ·
                  refine ⟨3952025537623625436404257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5269367383498167248539009 3952025537623625436404257)
                  ·
                    refine ⟨2964019153217719077303193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3952025537623625436404257 2964019153217719077303193)
                    ·
                      refine ⟨2223014364913289307977395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964019153217719077303193 2223014364913289307977395)
                      ·
                        rfl

theorem cell23_4329305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_4329305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329305 prefixEnd_4329305 := by exact prefixLift 4329305
  have htrace : WordTrace (prefixWord ++ tailWord_4329305) baseStart_4329305 baseEnd_4329305 := by
    simpa [prefixWord, tailWord_4329305, baseEnd_4329305] using wordTrace_append hprefix tailTrace_4329305
  have hstable : (prefixWord ++ tailWord_4329305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329305).length < 2 ^ (prefixWord ++ tailWord_4329305).sum := by decide
  have hdescent : baseEnd_4329305 < baseStart_4329305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329322 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4329322 : Nat := 118140960795 + 4329322 * 2 ^ 59
def prefixEnd_4329322 : Nat := 4983230072969 + 3 ^ 40 * 4329322 * 2
def baseEnd_4329322 : Nat := 2223023094084415741464817

theorem tailTrace_4329322 : CollatzResearch.WordTrace tailWord_4329322 prefixEnd_4329322 2223023094084415741464817 := by
  unfold tailWord_4329322
  simp only [CollatzResearch.WordTrace]
  refine ⟨39475836405403314544229555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 105268897081075505451278813 39475836405403314544229555)
  ·
    refine ⟨59213754608104971816344333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39475836405403314544229555 59213754608104971816344333)
    ·
      refine ⟨22205157978039364431129125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59213754608104971816344333 22205157978039364431129125)
      ·
        refine ⟨4163467120882380830836711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22205157978039364431129125 4163467120882380830836711)
        ·
          refine ⟨6245200681323571246255067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163467120882380830836711 6245200681323571246255067)
          ·
            refine ⟨9367801021985356869382601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6245200681323571246255067 9367801021985356869382601)
            ·
              refine ⟨7025850766489017652036951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9367801021985356869382601 7025850766489017652036951)
              ·
                refine ⟨10538776149733526478055427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7025850766489017652036951 10538776149733526478055427)
                ·
                  refine ⟨15808164224600289717083141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10538776149733526478055427 15808164224600289717083141)
                  ·
                    refine ⟨2964030792112554321953089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15808164224600289717083141 2964030792112554321953089)
                    ·
                      refine ⟨2223023094084415741464817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964030792112554321953089 2223023094084415741464817)
                      ·
                        rfl

theorem cell23_4329322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4329322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329322 prefixEnd_4329322 := by exact prefixLift 4329322
  have htrace : WordTrace (prefixWord ++ tailWord_4329322) baseStart_4329322 baseEnd_4329322 := by
    simpa [prefixWord, tailWord_4329322, baseEnd_4329322] using wordTrace_append hprefix tailTrace_4329322
  have hstable : (prefixWord ++ tailWord_4329322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329322).length < 2 ^ (prefixWord ++ tailWord_4329322).sum := by decide
  have hdescent : baseEnd_4329322 < baseStart_4329322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329331 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 4, 5, 2]
def baseStart_4329331 : Nat := 118140960795 + 4329331 * 2 ^ 59
def prefixEnd_4329331 : Nat := 4983230072969 + 3 ^ 40 * 4329331 * 2
def baseEnd_4329331 : Nat := 2223027715410306206252275

theorem tailTrace_4329331 : CollatzResearch.WordTrace tailWord_4329331 prefixEnd_4329331 2223027715410306206252275 := by
  unfold tailWord_4329331
  simp only [CollatzResearch.WordTrace]
  refine ⟨157903673878580652713995847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105269115919053768475997231 157903673878580652713995847)
  ·
    refine ⟨236855510817870979070993771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157903673878580652713995847 236855510817870979070993771)
    ·
      refine ⟨355283266226806468606490657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236855510817870979070993771 355283266226806468606490657)
      ·
        refine ⟨266462449670104851454867993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355283266226806468606490657 266462449670104851454867993)
        ·
          refine ⟨199846837252578638591150995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266462449670104851454867993 199846837252578638591150995)
          ·
            refine ⟨299770255878867957886726493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199846837252578638591150995 299770255878867957886726493)
            ·
              refine ⟨112413845954575484207522435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299770255878867957886726493 112413845954575484207522435)
              ·
                refine ⟨168620768931863226311283653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112413845954575484207522435 168620768931863226311283653)
                ·
                  refine ⟨31616394174724354933365685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168620768931863226311283653 31616394174724354933365685)
                  ·
                    refine ⟨2964036953880408275003033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31616394174724354933365685 2964036953880408275003033)
                    ·
                      refine ⟨2223027715410306206252275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964036953880408275003033 2223027715410306206252275)
                      ·
                        rfl

theorem cell23_4329331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 5, 2].length) (baseStart_4329331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329331 prefixEnd_4329331 := by exact prefixLift 4329331
  have htrace : WordTrace (prefixWord ++ tailWord_4329331) baseStart_4329331 baseEnd_4329331 := by
    simpa [prefixWord, tailWord_4329331, baseEnd_4329331] using wordTrace_append hprefix tailTrace_4329331
  have hstable : (prefixWord ++ tailWord_4329331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329331).length < 2 ^ (prefixWord ++ tailWord_4329331).sum := by decide
  have hdescent : baseEnd_4329331 < baseStart_4329331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329361 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_4329361 : Nat := 118140960795 + 4329361 * 2 ^ 59
def prefixEnd_4329361 : Nat := 4983230072969 + 3 ^ 40 * 4329361 * 2
def baseEnd_4329361 : Nat := 2223043119829941088877137

theorem tailTrace_4329361 : CollatzResearch.WordTrace tailWord_4329361 prefixEnd_4329361 2223043119829941088877137 := by
  unfold tailWord_4329361
  simp only [CollatzResearch.WordTrace]
  refine ⟨157904768068471967837587937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105269845378981311891725291 157904768068471967837587937)
  ·
    refine ⟨118428576051353975878190953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157904768068471967837587937 118428576051353975878190953)
    ·
      refine ⟨88821432038515481908643215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118428576051353975878190953 88821432038515481908643215)
      ·
        refine ⟨133232148057773222862964823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88821432038515481908643215 133232148057773222862964823)
        ·
          refine ⟨199848222086659834294447235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133232148057773222862964823 199848222086659834294447235)
          ·
            refine ⟨299772333129989751441670853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199848222086659834294447235 299772333129989751441670853)
            ·
              refine ⟨56207312461873078395313285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 299772333129989751441670853 56207312461873078395313285)
              ·
                refine ⟨10538871086601202199121241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56207312461873078395313285 10538871086601202199121241)
                ·
                  refine ⟨7904153314950901649340931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10538871086601202199121241 7904153314950901649340931)
                  ·
                    refine ⟨11856229972426352474011397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7904153314950901649340931 11856229972426352474011397)
                    ·
                      refine ⟨2223043119829941088877137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11856229972426352474011397 2223043119829941088877137)
                      ·
                        rfl

theorem cell23_4329361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_4329361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329361 prefixEnd_4329361 := by exact prefixLift 4329361
  have htrace : WordTrace (prefixWord ++ tailWord_4329361) baseStart_4329361 baseEnd_4329361 := by
    simpa [prefixWord, tailWord_4329361, baseEnd_4329361] using wordTrace_append hprefix tailTrace_4329361
  have hstable : (prefixWord ++ tailWord_4329361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329361).length < 2 ^ (prefixWord ++ tailWord_4329361).sum := by decide
  have hdescent : baseEnd_4329361 < baseStart_4329361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329422 : List Nat := [4, 1, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_4329422 : Nat := 118140960795 + 4329422 * 2 ^ 59
def prefixEnd_4329422 : Nat := 4983230072969 + 3 ^ 40 * 4329422 * 2
def baseEnd_4329422 : Nat := 741024814049955116738119

theorem tailTrace_4329422 : CollatzResearch.WordTrace tailWord_4329422 prefixEnd_4329422 741024814049955116738119 := by
  unfold tailWord_4329422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19738374115156371906944815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 105271328614167316837039013 19738374115156371906944815)
  ·
    refine ⟨29607561172734557860417223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19738374115156371906944815 29607561172734557860417223)
    ·
      refine ⟨44411341759101836790625835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29607561172734557860417223 44411341759101836790625835)
      ·
        refine ⟨66617012638652755185938753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44411341759101836790625835 66617012638652755185938753)
        ·
          refine ⟨49962759478989566389454065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66617012638652755185938753 49962759478989566389454065)
          ·
            refine ⟨37472069609242174792090549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49962759478989566389454065 37472069609242174792090549)
            ·
              refine ⟨3513006525866453886758489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37472069609242174792090549 3513006525866453886758489)
              ·
                refine ⟨2634754894399840415068867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3513006525866453886758489 2634754894399840415068867)
                ·
                  refine ⟨3952132341599760622603301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2634754894399840415068867 3952132341599760622603301)
                  ·
                    refine ⟨741024814049955116738119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3952132341599760622603301 741024814049955116738119)
                    ·
                      rfl

theorem cell23_4329422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_4329422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329422 prefixEnd_4329422 := by exact prefixLift 4329422
  have htrace : WordTrace (prefixWord ++ tailWord_4329422) baseStart_4329422 baseEnd_4329422 := by
    simpa [prefixWord, tailWord_4329422, baseEnd_4329422] using wordTrace_append hprefix tailTrace_4329422
  have hstable : (prefixWord ++ tailWord_4329422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329422).length < 2 ^ (prefixWord ++ tailWord_4329422).sum := by decide
  have hdescent : baseEnd_4329422 < baseStart_4329422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329431 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 3, 5]
def baseStart_4329431 : Nat := 118140960795 + 4329431 * 2 ^ 59
def prefixEnd_4329431 : Nat := 4983230072969 + 3 ^ 40 * 4329431 * 2
def baseEnd_4329431 : Nat := 741026354491918605000605

theorem tailTrace_4329431 : CollatzResearch.WordTrace tailWord_4329431 prefixEnd_4329431 741026354491918605000605 := by
  unfold tailWord_4329431
  simp only [CollatzResearch.WordTrace]
  refine ⟨157907321178218369792636147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105271547452145579861757431 157907321178218369792636147)
  ·
    refine ⟨236860981767327554688954221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157907321178218369792636147 236860981767327554688954221)
    ·
      refine ⟨88822868162747833008357833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236860981767327554688954221 88822868162747833008357833)
      ·
        refine ⟨66617151122060874756268375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88822868162747833008357833 66617151122060874756268375)
        ·
          refine ⟨99925726683091312134402563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66617151122060874756268375 99925726683091312134402563)
          ·
            refine ⟨149888590024636968201603845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99925726683091312134402563 149888590024636968201603845)
            ·
              refine ⟨28104110629619431537800721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149888590024636968201603845 28104110629619431537800721)
              ·
                refine ⟨21078082972214573653350541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28104110629619431537800721 21078082972214573653350541)
                ·
                  refine ⟨7904281114580465120006453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21078082972214573653350541 7904281114580465120006453)
                  ·
                    refine ⟨741026354491918605000605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7904281114580465120006453 741026354491918605000605)
                    ·
                      rfl

theorem cell23_4329431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_4329431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329431 prefixEnd_4329431 := by exact prefixLift 4329431
  have htrace : WordTrace (prefixWord ++ tailWord_4329431) baseStart_4329431 baseEnd_4329431 := by
    simpa [prefixWord, tailWord_4329431, baseEnd_4329431] using wordTrace_append hprefix tailTrace_4329431
  have hstable : (prefixWord ++ tailWord_4329431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329431).length < 2 ^ (prefixWord ++ tailWord_4329431).sum := by decide
  have hdescent : baseEnd_4329431 < baseStart_4329431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4329455 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 2, 3, 2]
def baseStart_4329455 : Nat := 118140960795 + 4329455 * 2 ^ 59
def prefixEnd_4329455 : Nat := 4983230072969 + 3 ^ 40 * 4329455 * 2
def baseEnd_4329455 : Nat := 2223091387011463721101705

theorem tailTrace_4329455 : CollatzResearch.WordTrace tailWord_4329455 prefixEnd_4329455 2223091387011463721101705 := by
  unfold tailWord_4329455
  simp only [CollatzResearch.WordTrace]
  refine ⟨157908196530131421891509819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 105272131020087614594339879 157908196530131421891509819)
  ·
    refine ⟨236862294795197132837264729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157908196530131421891509819 236862294795197132837264729)
    ·
      refine ⟨177646721096397849627948547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236862294795197132837264729 177646721096397849627948547)
      ·
        refine ⟨266470081644596774441922821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177646721096397849627948547 266470081644596774441922821)
        ·
          refine ⟨49963140308361895207860529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 266470081644596774441922821 49963140308361895207860529)
          ·
            refine ⟨37472355231271421405895397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49963140308361895207860529 37472355231271421405895397)
            ·
              refine ⟨7026066605863391513605387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37472355231271421405895397 7026066605863391513605387)
              ·
                refine ⟨10539099908795087270408081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026066605863391513605387 10539099908795087270408081)
                ·
                  refine ⟨7904324931596315452806061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10539099908795087270408081 7904324931596315452806061)
                  ·
                    refine ⟨2964121849348618294802273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7904324931596315452806061 2964121849348618294802273)
                    ·
                      refine ⟨2223091387011463721101705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2964121849348618294802273 2223091387011463721101705)
                      ·
                        rfl

theorem cell23_4329455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3, 2].length) (baseStart_4329455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4329455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4329455 prefixEnd_4329455 := by exact prefixLift 4329455
  have htrace : WordTrace (prefixWord ++ tailWord_4329455) baseStart_4329455 baseEnd_4329455 := by
    simpa [prefixWord, tailWord_4329455, baseEnd_4329455] using wordTrace_append hprefix tailTrace_4329455
  have hstable : (prefixWord ++ tailWord_4329455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4329455).length < 2 ^ (prefixWord ++ tailWord_4329455).sum := by decide
  have hdescent : baseEnd_4329455 < baseStart_4329455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4329455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
