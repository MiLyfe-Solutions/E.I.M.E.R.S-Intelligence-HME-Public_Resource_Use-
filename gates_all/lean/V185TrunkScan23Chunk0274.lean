import V185TrunkScan23Chunk0273

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1621353 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 3, 5]
def baseStart_1621353 : Nat := 118140960795 + 1621353 * 2 ^ 59
def prefixEnd_1621353 : Nat := 4983230072969 + 3 ^ 40 * 1621353 * 2
def baseEnd_1621353 : Nat := 277511133203100060877013

theorem tailTrace_1621353 : CollatzResearch.WordTrace tailWord_1621353 prefixEnd_1621353 277511133203100060877013 := by
  unfold tailWord_1621353
  simp only [CollatzResearch.WordTrace]
  refine ⟨59135602095122460891972713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39423734730081640594648475 59135602095122460891972713)
  ·
    refine ⟨44351701571341845668979535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59135602095122460891972713 44351701571341845668979535)
    ·
      refine ⟨66527552357012768503469303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44351701571341845668979535 66527552357012768503469303)
      ·
        refine ⟨99791328535519152755203955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66527552357012768503469303 99791328535519152755203955)
        ·
          refine ⟨149686992803278729132805933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99791328535519152755203955 149686992803278729132805933)
          ·
            refine ⟨56132622301229523424802225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149686992803278729132805933 56132622301229523424802225)
            ·
              refine ⟨42099466725922142568601669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56132622301229523424802225 42099466725922142568601669)
              ·
                refine ⟨7893650011110401731612813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42099466725922142568601669 7893650011110401731612813)
                ·
                  refine ⟨2960118754166400649354805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7893650011110401731612813 2960118754166400649354805)
                  ·
                    refine ⟨277511133203100060877013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2960118754166400649354805 277511133203100060877013)
                    ·
                      rfl

theorem cell23_1621353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_1621353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621353 prefixEnd_1621353 := by exact prefixLift 1621353
  have htrace : WordTrace (prefixWord ++ tailWord_1621353) baseStart_1621353 baseEnd_1621353 := by
    simpa [prefixWord, tailWord_1621353, baseEnd_1621353] using wordTrace_append hprefix tailTrace_1621353
  have hstable : (prefixWord ++ tailWord_1621353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621353).length < 2 ^ (prefixWord ++ tailWord_1621353).sum := by decide
  have hdescent : baseEnd_1621353 < baseStart_1621353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621357 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 6]
def baseStart_1621357 : Nat := 118140960795 + 1621357 * 2 ^ 59
def prefixEnd_1621357 : Nat := 4983230072969 + 3 ^ 40 * 1621357 * 2
def baseEnd_1621357 : Nat := 92503939281324240775669

theorem tailTrace_1621357 : CollatzResearch.WordTrace tailWord_1621357 prefixEnd_1621357 92503939281324240775669 := by
  unfold tailWord_1621357
  simp only [CollatzResearch.WordTrace]
  refine ⟨59135747987107969575118325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39423831991405313050078883 59135747987107969575118325)
  ·
    refine ⟨5543976373791372147667343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59135747987107969575118325 5543976373791372147667343)
    ·
      refine ⟨8315964560687058221501015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543976373791372147667343 8315964560687058221501015)
      ·
        refine ⟨12473946841030587332251523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315964560687058221501015 12473946841030587332251523)
        ·
          refine ⟨18710920261545880998377285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473946841030587332251523 18710920261545880998377285)
          ·
            refine ⟨3508297549039852687195741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18710920261545880998377285 3508297549039852687195741)
            ·
              refine ⟨1315611580889944757698403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3508297549039852687195741 1315611580889944757698403)
              ·
                refine ⟨1973417371334917136547605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315611580889944757698403 1973417371334917136547605)
                ·
                  refine ⟨92503939281324240775669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1973417371334917136547605 92503939281324240775669)
                  ·
                    rfl

theorem cell23_1621357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_1621357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621357 prefixEnd_1621357 := by exact prefixLift 1621357
  have htrace : WordTrace (prefixWord ++ tailWord_1621357) baseStart_1621357 baseEnd_1621357 := by
    simpa [prefixWord, tailWord_1621357, baseEnd_1621357] using wordTrace_append hprefix tailTrace_1621357
  have hstable : (prefixWord ++ tailWord_1621357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621357).length < 2 ^ (prefixWord ++ tailWord_1621357).sum := by decide
  have hdescent : baseEnd_1621357 < baseStart_1621357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621360 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 3, 5, 2]
def baseStart_1621360 : Nat := 118140960795 + 1621360 * 2 ^ 59
def prefixEnd_1621360 : Nat := 4983230072969 + 3 ^ 40 * 1621360 * 2
def baseEnd_1621360 : Nat := 832536993973881655243507

theorem tailTrace_1621360 : CollatzResearch.WordTrace tailWord_1621360 prefixEnd_1621360 832536993973881655243507 := by
  unfold tailWord_1621360
  simp only [CollatzResearch.WordTrace]
  refine ⟨29567928703048550543738767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39423904937398067391651689 29567928703048550543738767)
  ·
    refine ⟨44351893054572825815608151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29567928703048550543738767 44351893054572825815608151)
    ·
      refine ⟨66527839581859238723412227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44351893054572825815608151 66527839581859238723412227)
      ·
        refine ⟨99791759372788858085118341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66527839581859238723412227 99791759372788858085118341)
        ·
          refine ⟨18710954882397910890959689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99791759372788858085118341 18710954882397910890959689)
          ·
            refine ⟨14033216161798433168219767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18710954882397910890959689 14033216161798433168219767)
            ·
              refine ⟨21049824242697649752329651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14033216161798433168219767 21049824242697649752329651)
              ·
                refine ⟨31574736364046474628494477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21049824242697649752329651 31574736364046474628494477)
                ·
                  refine ⟨11840526136517427985685429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31574736364046474628494477 11840526136517427985685429)
                  ·
                    refine ⟨1110049325298508873658009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11840526136517427985685429 1110049325298508873658009)
                    ·
                      refine ⟨832536993973881655243507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110049325298508873658009 832536993973881655243507)
                      ·
                        rfl

theorem cell23_1621360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 5, 2].length) (baseStart_1621360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621360 prefixEnd_1621360 := by exact prefixLift 1621360
  have htrace : WordTrace (prefixWord ++ tailWord_1621360) baseStart_1621360 baseEnd_1621360 := by
    simpa [prefixWord, tailWord_1621360, baseEnd_1621360] using wordTrace_append hprefix tailTrace_1621360
  have hstable : (prefixWord ++ tailWord_1621360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621360).length < 2 ^ (prefixWord ++ tailWord_1621360).sum := by decide
  have hdescent : baseEnd_1621360 < baseStart_1621360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621378 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1621378 : Nat := 118140960795 + 1621378 * 2 ^ 59
def prefixEnd_1621378 : Nat := 4983230072969 + 3 ^ 40 * 1621378 * 2
def baseEnd_1621378 : Nat := 277515412208554194939475

theorem tailTrace_1621378 : CollatzResearch.WordTrace tailWord_1621378 prefixEnd_1621378 277515412208554194939475 := by
  unfold tailWord_1621378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14784128480007972540408197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39424342613354593441088525 14784128480007972540408197)
  ·
    refine ⟨2772024090001494851326537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14784128480007972540408197 2772024090001494851326537)
    ·
      refine ⟨2079018067501121138494903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772024090001494851326537 2079018067501121138494903)
      ·
        refine ⟨3118527101251681707742355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079018067501121138494903 3118527101251681707742355)
        ·
          refine ⟨4677790651877522561613533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118527101251681707742355 4677790651877522561613533)
          ·
            refine ⟨1754171494454070960605075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4677790651877522561613533 1754171494454070960605075)
            ·
              refine ⟨2631257241681106440907613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754171494454070960605075 2631257241681106440907613)
              ·
                refine ⟨986721465630414915340355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631257241681106440907613 986721465630414915340355)
                ·
                  refine ⟨1480082198445622373010533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986721465630414915340355 1480082198445622373010533)
                  ·
                    refine ⟨277515412208554194939475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1480082198445622373010533 277515412208554194939475)
                    ·
                      rfl

theorem cell23_1621378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1621378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621378 prefixEnd_1621378 := by exact prefixLift 1621378
  have htrace : WordTrace (prefixWord ++ tailWord_1621378) baseStart_1621378 baseEnd_1621378 := by
    simpa [prefixWord, tailWord_1621378, baseEnd_1621378] using wordTrace_append hprefix tailTrace_1621378
  have hstable : (prefixWord ++ tailWord_1621378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621378).length < 2 ^ (prefixWord ++ tailWord_1621378).sum := by decide
  have hdescent : baseEnd_1621378 < baseStart_1621378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621393 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_1621393 : Nat := 118140960795 + 1621393 * 2 ^ 59
def prefixEnd_1621393 : Nat := 4983230072969 + 3 ^ 40 * 1621393 * 2
def baseEnd_1621393 : Nat := 832553938835480026130855

theorem tailTrace_1621393 : CollatzResearch.WordTrace tailWord_1621393 prefixEnd_1621393 832553938835480026130855 := by
  unfold tailWord_1621393
  simp only [CollatzResearch.WordTrace]
  refine ⟨59137061014977547723428833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39424707343318365148952555 59137061014977547723428833)
  ·
    refine ⟨44352795761233160792571625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59137061014977547723428833 44352795761233160792571625)
    ·
      refine ⟨33264596820924870594428719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44352795761233160792571625 33264596820924870594428719)
      ·
        refine ⟨49896895231387305891643079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33264596820924870594428719 49896895231387305891643079)
        ·
          refine ⟨74845342847080958837464619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49896895231387305891643079 74845342847080958837464619)
          ·
            refine ⟨112268014270621438256196929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74845342847080958837464619 112268014270621438256196929)
            ·
              refine ⟨84201010702966078692147697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112268014270621438256196929 84201010702966078692147697)
              ·
                refine ⟨63150758027224559019110773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84201010702966078692147697 63150758027224559019110773)
                ·
                  refine ⟨5920383565052302408041635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63150758027224559019110773 5920383565052302408041635)
                  ·
                    refine ⟨8880575347578453612062453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920383565052302408041635 8880575347578453612062453)
                    ·
                      refine ⟨832553938835480026130855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8880575347578453612062453 832553938835480026130855)
                      ·
                        rfl

theorem cell23_1621393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_1621393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621393 prefixEnd_1621393 := by exact prefixLift 1621393
  have htrace : WordTrace (prefixWord ++ tailWord_1621393) baseStart_1621393 baseEnd_1621393 := by
    simpa [prefixWord, tailWord_1621393, baseEnd_1621393] using wordTrace_append hprefix tailTrace_1621393
  have hstable : (prefixWord ++ tailWord_1621393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621393).length < 2 ^ (prefixWord ++ tailWord_1621393).sum := by decide
  have hdescent : baseEnd_1621393 < baseStart_1621393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621401 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 1, 1, 3]
def baseStart_1621401 : Nat := 118140960795 + 1621401 * 2 ^ 59
def prefixEnd_1621401 : Nat := 4983230072969 + 3 ^ 40 * 1621401 * 2
def baseEnd_1621401 : Nat := 832558046680715994830819

theorem tailTrace_1621401 : CollatzResearch.WordTrace tailWord_1621401 prefixEnd_1621401 832558046680715994830819 := by
  unfold tailWord_1621401
  simp only [CollatzResearch.WordTrace]
  refine ⟨59137352798948565089720057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39424901865965710059813371 59137352798948565089720057)
  ·
    refine ⟨44353014599211423817290043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59137352798948565089720057 44353014599211423817290043)
    ·
      refine ⟨66529521898817135725935065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44353014599211423817290043 66529521898817135725935065)
      ·
        refine ⟨49897141424112851794451299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66529521898817135725935065 49897141424112851794451299)
        ·
          refine ⟨74845712136169277691676949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49897141424112851794451299 74845712136169277691676949)
          ·
            refine ⟨3508392756382934891797357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74845712136169277691676949 3508392756382934891797357)
            ·
              refine ⟨1315647283643600584424009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3508392756382934891797357 1315647283643600584424009)
              ·
                refine ⟨986735462732700438318007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315647283643600584424009 986735462732700438318007)
                ·
                  refine ⟨1480103194099050657477011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986735462732700438318007 1480103194099050657477011)
                  ·
                    refine ⟨2220154791148575986215517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1480103194099050657477011 2220154791148575986215517)
                    ·
                      refine ⟨832558046680715994830819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220154791148575986215517 832558046680715994830819)
                      ·
                        rfl

theorem cell23_1621401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_1621401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621401 prefixEnd_1621401 := by exact prefixLift 1621401
  have htrace : WordTrace (prefixWord ++ tailWord_1621401) baseStart_1621401 baseEnd_1621401 := by
    simpa [prefixWord, tailWord_1621401, baseEnd_1621401] using wordTrace_append hprefix tailTrace_1621401
  have hstable : (prefixWord ++ tailWord_1621401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621401).length < 2 ^ (prefixWord ++ tailWord_1621401).sum := by decide
  have hdescent : baseEnd_1621401 < baseStart_1621401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621440 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_1621440 : Nat := 118140960795 + 1621440 * 2 ^ 59
def prefixEnd_1621440 : Nat := 4983230072969 + 3 ^ 40 * 1621440 * 2
def baseEnd_1621440 : Nat := 832578072426241342243139

theorem tailTrace_1621440 : CollatzResearch.WordTrace tailWord_1621440 prefixEnd_1621440 832578072426241342243139 := by
  unfold tailWord_1621440
  simp only [CollatzResearch.WordTrace]
  refine ⟨29569387622903637375194887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39425850163871516500259849 29569387622903637375194887)
  ·
    refine ⟨44354081434355456062792331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29569387622903637375194887 44354081434355456062792331)
    ·
      refine ⟨66531122151533184094188497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44354081434355456062792331 66531122151533184094188497)
      ·
        refine ⟨49898341613649888070641373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66531122151533184094188497 49898341613649888070641373)
        ·
          refine ⟨18711878105118708026490515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49898341613649888070641373 18711878105118708026490515)
          ·
            refine ⟨28067817157678062039735773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18711878105118708026490515 28067817157678062039735773)
            ·
              refine ⟨10525431434129273264900915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28067817157678062039735773 10525431434129273264900915)
              ·
                refine ⟨15788147151193909897351373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10525431434129273264900915 15788147151193909897351373)
                ·
                  refine ⟨5920555181697716211506765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15788147151193909897351373 5920555181697716211506765)
                  ·
                    refine ⟨2220208193136643579315037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5920555181697716211506765 2220208193136643579315037)
                    ·
                      refine ⟨832578072426241342243139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220208193136643579315037 832578072426241342243139)
                      ·
                        rfl

theorem cell23_1621440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_1621440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621440 prefixEnd_1621440 := by exact prefixLift 1621440
  have htrace : WordTrace (prefixWord ++ tailWord_1621440) baseStart_1621440 baseEnd_1621440 := by
    simpa [prefixWord, tailWord_1621440, baseEnd_1621440] using wordTrace_append hprefix tailTrace_1621440
  have hstable : (prefixWord ++ tailWord_1621440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621440).length < 2 ^ (prefixWord ++ tailWord_1621440).sum := by decide
  have hdescent : baseEnd_1621440 < baseStart_1621440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621444 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1621444 : Nat := 118140960795 + 1621444 * 2 ^ 59
def prefixEnd_1621444 : Nat := 4983230072969 + 3 ^ 40 * 1621444 * 2
def baseEnd_1621444 : Nat := 832580126348859326593121

theorem tailTrace_1621444 : CollatzResearch.WordTrace tailWord_1621444 prefixEnd_1621444 832580126348859326593121 := by
  unfold tailWord_1621444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29569460568896391716767693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39425947425195188955690257 29569460568896391716767693)
  ·
    refine ⟨11088547713336146893787885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29569460568896391716767693 11088547713336146893787885)
    ·
      refine ⟨4158205392501055085170457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11088547713336146893787885 4158205392501055085170457)
      ·
        refine ⟨3118654044375791313877843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4158205392501055085170457 3118654044375791313877843)
        ·
          refine ⟨4677981066563686970816765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118654044375791313877843 4677981066563686970816765)
          ·
            refine ⟨1754242899961382614056287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4677981066563686970816765 1754242899961382614056287)
            ·
              refine ⟨2631364349942073921084431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754242899961382614056287 2631364349942073921084431)
              ·
                refine ⟨3947046524913110881626647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631364349942073921084431 3947046524913110881626647)
                ·
                  refine ⟨5920569787369666322439971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947046524913110881626647 5920569787369666322439971)
                  ·
                    refine ⟨8880854681054499483659957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920569787369666322439971 8880854681054499483659957)
                    ·
                      refine ⟨832580126348859326593121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8880854681054499483659957 832580126348859326593121)
                      ·
                        rfl

theorem cell23_1621444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1621444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621444 prefixEnd_1621444 := by exact prefixLift 1621444
  have htrace : WordTrace (prefixWord ++ tailWord_1621444) baseStart_1621444 baseEnd_1621444 := by
    simpa [prefixWord, tailWord_1621444, baseEnd_1621444] using wordTrace_append hprefix tailTrace_1621444
  have hstable : (prefixWord ++ tailWord_1621444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621444).length < 2 ^ (prefixWord ++ tailWord_1621444).sum := by decide
  have hdescent : baseEnd_1621444 < baseStart_1621444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621480 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1621480 : Nat := 118140960795 + 1621480 * 2 ^ 59
def prefixEnd_1621480 : Nat := 4983230072969 + 3 ^ 40 * 1621480 * 2
def baseEnd_1621480 : Nat := 832598611652421185742955

theorem tailTrace_1621480 : CollatzResearch.WordTrace tailWord_1621480 prefixEnd_1621480 832598611652421185742955 := by
  unfold tailWord_1621480
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570117082831180790922947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39426822777108241054563929 29570117082831180790922947)
  ·
    refine ⟨44355175624246771186384421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29570117082831180790922947 44355175624246771186384421)
    ·
      refine ⟨8316595429546269597447079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44355175624246771186384421 8316595429546269597447079)
      ·
        refine ⟨12474893144319404396170619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8316595429546269597447079 12474893144319404396170619)
        ·
          refine ⟨18712339716479106594255929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12474893144319404396170619 18712339716479106594255929)
          ·
            refine ⟨14034254787359329945691947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18712339716479106594255929 14034254787359329945691947)
            ·
              refine ⟨21051382181038994918537921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14034254787359329945691947 21051382181038994918537921)
              ·
                refine ⟨15788536635779246188903441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21051382181038994918537921 15788536635779246188903441)
                ·
                  refine ⟨11841402476834434641677581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15788536635779246188903441 11841402476834434641677581)
                  ·
                    refine ⟨4440525928812912990629093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11841402476834434641677581 4440525928812912990629093)
                    ·
                      refine ⟨832598611652421185742955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4440525928812912990629093 832598611652421185742955)
                      ·
                        rfl

theorem cell23_1621480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1621480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621480 prefixEnd_1621480 := by exact prefixLift 1621480
  have htrace : WordTrace (prefixWord ++ tailWord_1621480) baseStart_1621480 baseEnd_1621480 := by
    simpa [prefixWord, tailWord_1621480, baseEnd_1621480] using wordTrace_append hprefix tailTrace_1621480
  have hstable : (prefixWord ++ tailWord_1621480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621480).length < 2 ^ (prefixWord ++ tailWord_1621480).sum := by decide
  have hdescent : baseEnd_1621480 < baseStart_1621480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621500 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_1621500 : Nat := 118140960795 + 1621500 * 2 ^ 59
def prefixEnd_1621500 : Nat := 4983230072969 + 3 ^ 40 * 1621500 * 2
def baseEnd_1621500 : Nat := 832608881265511107492863

theorem tailTrace_1621500 : CollatzResearch.WordTrace tailWord_1621500 prefixEnd_1621500 832608881265511107492863 := by
  unfold tailWord_1621500
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570481812794952498786977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39427309083726603331715969 29570481812794952498786977)
  ·
    refine ⟨22177861359596214374090233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29570481812794952498786977 22177861359596214374090233)
    ·
      refine ⟨16633396019697160780567675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22177861359596214374090233 16633396019697160780567675)
      ·
        refine ⟨24950094029545741170851513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16633396019697160780567675 24950094029545741170851513)
        ·
          refine ⟨18712570522159305878138635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24950094029545741170851513 18712570522159305878138635)
          ·
            refine ⟨28068855783238958817207953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18712570522159305878138635 28068855783238958817207953)
            ·
              refine ⟨21051641837429219112905965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28068855783238958817207953 21051641837429219112905965)
              ·
                refine ⟨7894365689035957167339737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21051641837429219112905965 7894365689035957167339737)
                ·
                  refine ⟨5920774266776967875504803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7894365689035957167339737 5920774266776967875504803)
                  ·
                    refine ⟨8881161400165451813257205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920774266776967875504803 8881161400165451813257205)
                    ·
                      refine ⟨832608881265511107492863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8881161400165451813257205 832608881265511107492863)
                      ·
                        rfl

theorem cell23_1621500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_1621500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621500 prefixEnd_1621500 := by exact prefixLift 1621500
  have htrace : WordTrace (prefixWord ++ tailWord_1621500) baseStart_1621500 baseEnd_1621500 := by
    simpa [prefixWord, tailWord_1621500, baseEnd_1621500] using wordTrace_append hprefix tailTrace_1621500
  have hstable : (prefixWord ++ tailWord_1621500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621500).length < 2 ^ (prefixWord ++ tailWord_1621500).sum := by decide
  have hdescent : baseEnd_1621500 < baseStart_1621500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621501 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_1621501 : Nat := 118140960795 + 1621501 * 2 ^ 59
def prefixEnd_1621501 : Nat := 4983230072969 + 3 ^ 40 * 1621501 * 2
def baseEnd_1621501 : Nat := 832609394746165603580359

theorem tailTrace_1621501 : CollatzResearch.WordTrace tailWord_1621501 prefixEnd_1621501 832609394746165603580359 := by
  unfold tailWord_1621501
  simp only [CollatzResearch.WordTrace]
  refine ⟨59141000098586282168360357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39427333399057521445573571 59141000098586282168360357)
  ·
    refine ⟨11088937518484927906567567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59141000098586282168360357 11088937518484927906567567)
    ·
      refine ⟨16633406277727391859851351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11088937518484927906567567 16633406277727391859851351)
      ·
        refine ⟨24950109416591087789777027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16633406277727391859851351 24950109416591087789777027)
        ·
          refine ⟨37425164124886631684665541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24950109416591087789777027 37425164124886631684665541)
          ·
            refine ⟨7017218273416243440874789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37425164124886631684665541 7017218273416243440874789)
            ·
              refine ⟨1315728426265545645164023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7017218273416243440874789 1315728426265545645164023)
              ·
                refine ⟨1973592639398318467746035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315728426265545645164023 1973592639398318467746035)
                ·
                  refine ⟨2960388959097477701619053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973592639398318467746035 2960388959097477701619053)
                  ·
                    refine ⟨1110145859661554138107145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960388959097477701619053 1110145859661554138107145)
                    ·
                      refine ⟨832609394746165603580359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110145859661554138107145 832609394746165603580359)
                      ·
                        rfl

theorem cell23_1621501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_1621501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621501 prefixEnd_1621501 := by exact prefixLift 1621501
  have htrace : WordTrace (prefixWord ++ tailWord_1621501) baseStart_1621501 baseEnd_1621501 := by
    simpa [prefixWord, tailWord_1621501, baseEnd_1621501] using wordTrace_append hprefix tailTrace_1621501
  have hstable : (prefixWord ++ tailWord_1621501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621501).length < 2 ^ (prefixWord ++ tailWord_1621501).sum := by decide
  have hdescent : baseEnd_1621501 < baseStart_1621501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621508 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1621508 : Nat := 118140960795 + 1621508 * 2 ^ 59
def prefixEnd_1621508 : Nat := 4983230072969 + 3 ^ 40 * 1621508 * 2
def baseEnd_1621508 : Nat := 832612989110747076192827

theorem tailTrace_1621508 : CollatzResearch.WordTrace tailWord_1621508 prefixEnd_1621508 832612989110747076192827 := by
  unfold tailWord_1621508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570627704780461181932589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39427503606373948242576785 29570627704780461181932589)
  ·
    refine ⟨11088985389292672943224721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29570627704780461181932589 11088985389292672943224721)
    ·
      refine ⟨8316739041969504707418541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11088985389292672943224721 8316739041969504707418541)
      ·
        refine ⟨3118777140738564265281953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8316739041969504707418541 3118777140738564265281953)
        ·
          refine ⟨2339082855553923198961465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118777140738564265281953 2339082855553923198961465)
          ·
            refine ⟨1754312141665442399221099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2339082855553923198961465 1754312141665442399221099)
            ·
              refine ⟨2631468212498163598831649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754312141665442399221099 2631468212498163598831649)
              ·
                refine ⟨1973601159373622699123737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631468212498163598831649 1973601159373622699123737)
                ·
                  refine ⟨1480200869530217024342803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1973601159373622699123737 1480200869530217024342803)
                  ·
                    refine ⟨2220301304295325536514205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1480200869530217024342803 2220301304295325536514205)
                    ·
                      refine ⟨832612989110747076192827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220301304295325536514205 832612989110747076192827)
                      ·
                        rfl

theorem cell23_1621508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1621508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621508 prefixEnd_1621508 := by exact prefixLift 1621508
  have htrace : WordTrace (prefixWord ++ tailWord_1621508) baseStart_1621508 baseEnd_1621508 := by
    simpa [prefixWord, tailWord_1621508, baseEnd_1621508] using wordTrace_append hprefix tailTrace_1621508
  have hstable : (prefixWord ++ tailWord_1621508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621508).length < 2 ^ (prefixWord ++ tailWord_1621508).sum := by decide
  have hdescent : baseEnd_1621508 < baseStart_1621508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621567 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 2, 5]
def baseStart_1621567 : Nat := 118140960795 + 1621567 * 2 ^ 59
def prefixEnd_1621567 : Nat := 4983230072969 + 3 ^ 40 * 1621567 * 2
def baseEnd_1621567 : Nat := 277547761489787448451685

theorem tailTrace_1621567 : CollatzResearch.WordTrace tailWord_1621567 prefixEnd_1621567 277547761489787448451685 := by
  unfold tailWord_1621567
  simp only [CollatzResearch.WordTrace]
  refine ⟨59143407316347175440262955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39428938210898116960175303 59143407316347175440262955)
  ·
    refine ⟨88715110974520763160394433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59143407316347175440262955 88715110974520763160394433)
    ·
      refine ⟨66536333230890572370295825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88715110974520763160394433 66536333230890572370295825)
      ·
        refine ⟨49902249923167929277721869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66536333230890572370295825 49902249923167929277721869)
        ·
          refine ⟨18713343721187973479145701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49902249923167929277721869 18713343721187973479145701)
          ·
            refine ⟨3508751947722745027339819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18713343721187973479145701 3508751947722745027339819)
            ·
              refine ⟨5263127921584117541009729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508751947722745027339819 5263127921584117541009729)
              ·
                refine ⟨3947345941188088155757297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263127921584117541009729 3947345941188088155757297)
                ·
                  refine ⟨2960509455891066116817973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947345941188088155757297 2960509455891066116817973)
                  ·
                    refine ⟨277547761489787448451685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2960509455891066116817973 277547761489787448451685)
                    ·
                      rfl

theorem cell23_1621567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_1621567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621567 prefixEnd_1621567 := by exact prefixLift 1621567
  have htrace : WordTrace (prefixWord ++ tailWord_1621567) baseStart_1621567 baseEnd_1621567 := by
    simpa [prefixWord, tailWord_1621567, baseEnd_1621567] using wordTrace_append hprefix tailTrace_1621567
  have hstable : (prefixWord ++ tailWord_1621567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621567).length < 2 ^ (prefixWord ++ tailWord_1621567).sum := by decide
  have hdescent : baseEnd_1621567 < baseStart_1621567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621600 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1621600 : Nat := 118140960795 + 1621600 * 2 ^ 59
def prefixEnd_1621600 : Nat := 4983230072969 + 3 ^ 40 * 1621600 * 2
def baseEnd_1621600 : Nat := 832660229330960716242403

theorem tailTrace_1621600 : CollatzResearch.WordTrace tailWord_1621600 prefixEnd_1621600 832660229330960716242403 := by
  unfold tailWord_1621600
  simp only [CollatzResearch.WordTrace]
  refine ⟨29572305462613811038107127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39429740616818414717476169 29572305462613811038107127)
  ·
    refine ⟨44358458193920716557160691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29572305462613811038107127 44358458193920716557160691)
    ·
      refine ⟨66537687290881074835741037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44358458193920716557160691 66537687290881074835741037)
      ·
        refine ⟨24951632734080403063402889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66537687290881074835741037 24951632734080403063402889)
        ·
          refine ⟨18713724550560302297552167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24951632734080403063402889 18713724550560302297552167)
          ·
            refine ⟨28070586825840453446328251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713724550560302297552167 28070586825840453446328251)
            ·
              refine ⟨42105880238760680169492377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28070586825840453446328251 42105880238760680169492377)
              ·
                refine ⟨31579410179070510127119283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42105880238760680169492377 31579410179070510127119283)
                ·
                  refine ⟨47369115268605765190678925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31579410179070510127119283 47369115268605765190678925)
                  ·
                    refine ⟨17763418225727161946504597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47369115268605765190678925 17763418225727161946504597)
                    ·
                      refine ⟨832660229330960716242403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17763418225727161946504597 832660229330960716242403)
                      ·
                        rfl

theorem cell23_1621600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1621600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621600 prefixEnd_1621600 := by exact prefixLift 1621600
  have htrace : WordTrace (prefixWord ++ tailWord_1621600) baseStart_1621600 baseEnd_1621600 := by
    simpa [prefixWord, tailWord_1621600, baseEnd_1621600] using wordTrace_append hprefix tailTrace_1621600
  have hstable : (prefixWord ++ tailWord_1621600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621600).length < 2 ^ (prefixWord ++ tailWord_1621600).sum := by decide
  have hdescent : baseEnd_1621600 < baseStart_1621600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621604 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_1621604 : Nat := 118140960795 + 1621604 * 2 ^ 59
def prefixEnd_1621604 : Nat := 4983230072969 + 3 ^ 40 * 1621604 * 2
def baseEnd_1621604 : Nat := 832662283253578700592385

theorem tailTrace_1621604 : CollatzResearch.WordTrace tailWord_1621604 prefixEnd_1621604 832662283253578700592385 := by
  unfold tailWord_1621604
  simp only [CollatzResearch.WordTrace]
  refine ⟨29572378408606565379679933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39429837878142087172906577 29572378408606565379679933)
  ·
    refine ⟨11089641903227462017379975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29572378408606565379679933 11089641903227462017379975)
    ·
      refine ⟨16634462854841193026069963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11089641903227462017379975 16634462854841193026069963)
      ·
        refine ⟨24951694282261789539104945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16634462854841193026069963 24951694282261789539104945)
        ·
          refine ⟨18713770711696342154328709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24951694282261789539104945 18713770711696342154328709)
          ·
            refine ⟨3508832008443064153936633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18713770711696342154328709 3508832008443064153936633)
            ·
              refine ⟨2631624006332298115452475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508832008443064153936633 2631624006332298115452475)
              ·
                refine ⟨3947436009498447173178713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631624006332298115452475 3947436009498447173178713)
                ·
                  refine ⟨2960577007123835379884035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947436009498447173178713 2960577007123835379884035)
                  ·
                    refine ⟨4440865510685753069826053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2960577007123835379884035 4440865510685753069826053)
                    ·
                      refine ⟨832662283253578700592385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4440865510685753069826053 832662283253578700592385)
                      ·
                        rfl

theorem cell23_1621604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_1621604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621604 prefixEnd_1621604 := by exact prefixLift 1621604
  have htrace : WordTrace (prefixWord ++ tailWord_1621604) baseStart_1621604 baseEnd_1621604 := by
    simpa [prefixWord, tailWord_1621604, baseEnd_1621604] using wordTrace_append hprefix tailTrace_1621604
  have hstable : (prefixWord ++ tailWord_1621604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621604).length < 2 ^ (prefixWord ++ tailWord_1621604).sum := by decide
  have hdescent : baseEnd_1621604 < baseStart_1621604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621607 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1621607 : Nat := 118140960795 + 1621607 * 2 ^ 59
def prefixEnd_1621607 : Nat := 4983230072969 + 3 ^ 40 * 1621607 * 2
def baseEnd_1621607 : Nat := 832663823695542188854871

theorem tailTrace_1621607 : CollatzResearch.WordTrace tailWord_1621607 prefixEnd_1621607 832663823695542188854871 := by
  unfold tailWord_1621607
  simp only [CollatzResearch.WordTrace]
  refine ⟨59144866236202262271719075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39429910824134841514479383 59144866236202262271719075)
  ·
    refine ⟨88717299354303393407578613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59144866236202262271719075 88717299354303393407578613)
    ·
      refine ⟨8317246814465943131960495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88717299354303393407578613 8317246814465943131960495)
      ·
        refine ⟨12475870221698914697940743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8317246814465943131960495 12475870221698914697940743)
        ·
          refine ⟨18713805332548372046911115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12475870221698914697940743 18713805332548372046911115)
          ·
            refine ⟨28070707998822558070366673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713805332548372046911115 28070707998822558070366673)
            ·
              refine ⟨21053030999116918552775005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28070707998822558070366673 21053030999116918552775005)
              ·
                refine ⟨7894886624668844457290627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21053030999116918552775005 7894886624668844457290627)
                ·
                  refine ⟨11842329937003266685935941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894886624668844457290627 11842329937003266685935941)
                  ·
                    refine ⟨2220436863188112503612989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11842329937003266685935941 2220436863188112503612989)
                    ·
                      refine ⟨832663823695542188854871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220436863188112503612989 832663823695542188854871)
                      ·
                        rfl

theorem cell23_1621607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1621607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621607 prefixEnd_1621607 := by exact prefixLift 1621607
  have htrace : WordTrace (prefixWord ++ tailWord_1621607) baseStart_1621607 baseEnd_1621607 := by
    simpa [prefixWord, tailWord_1621607, baseEnd_1621607] using wordTrace_append hprefix tailTrace_1621607
  have hstable : (prefixWord ++ tailWord_1621607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621607).length < 2 ^ (prefixWord ++ tailWord_1621607).sum := by decide
  have hdescent : baseEnd_1621607 < baseStart_1621607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621627 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 6]
def baseStart_1621627 : Nat := 118140960795 + 1621627 * 2 ^ 59
def prefixEnd_1621627 : Nat := 4983230072969 + 3 ^ 40 * 1621627 * 2
def baseEnd_1621627 : Nat := 92519343700959123400531

theorem tailTrace_1621627 : CollatzResearch.WordTrace tailWord_1621627 prefixEnd_1621627 92519343700959123400531 := by
  unfold tailWord_1621627
  simp only [CollatzResearch.WordTrace]
  refine ⟨59145595696129805687447135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39430397130753203791631423 59145595696129805687447135)
  ·
    refine ⟨88718393544194708531170703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59145595696129805687447135 88718393544194708531170703)
    ·
      refine ⟨133077590316292062796756055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88718393544194708531170703 133077590316292062796756055)
      ·
        refine ⟨199616385474438094195134083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133077590316292062796756055 199616385474438094195134083)
        ·
          refine ⟨299424578211657141292701125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199616385474438094195134083 299424578211657141292701125)
          ·
            refine ⟨56142108414685713992381461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299424578211657141292701125 56142108414685713992381461)
            ·
              refine ⟨2631661331938392843392881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56142108414685713992381461 2631661331938392843392881)
              ·
                refine ⟨1973745998953794632544661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631661331938392843392881 1973745998953794632544661)
                ·
                  refine ⟨92519343700959123400531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1973745998953794632544661 92519343700959123400531)
                  ·
                    rfl

theorem cell23_1621627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 6].length) (baseStart_1621627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621627 prefixEnd_1621627 := by exact prefixLift 1621627
  have htrace : WordTrace (prefixWord ++ tailWord_1621627) baseStart_1621627 baseEnd_1621627 := by
    simpa [prefixWord, tailWord_1621627, baseEnd_1621627] using wordTrace_append hprefix tailTrace_1621627
  have hstable : (prefixWord ++ tailWord_1621627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621627).length < 2 ^ (prefixWord ++ tailWord_1621627).sum := by decide
  have hdescent : baseEnd_1621627 < baseStart_1621627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621678 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_1621678 : Nat := 118140960795 + 1621678 * 2 ^ 59
def prefixEnd_1621678 : Nat := 4983230072969 + 3 ^ 40 * 1621678 * 2
def baseEnd_1621678 : Nat := 92522253424667934563005

theorem tailTrace_1621678 : CollatzResearch.WordTrace tailWord_1621678 prefixEnd_1621678 92522253424667934563005 := by
  unfold tailWord_1621678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393431977368130174694211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39431637212630027598369125 7393431977368130174694211)
  ·
    refine ⟨11090147966052195262041317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393431977368130174694211 11090147966052195262041317)
    ·
      refine ⟨2079402743634786611632747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11090147966052195262041317 2079402743634786611632747)
      ·
        refine ⟨3119104115452179917449121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079402743634786611632747 3119104115452179917449121)
        ·
          refine ⟨2339328086589134938086841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119104115452179917449121 2339328086589134938086841)
          ·
            refine ⟨1754496064941851203565131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2339328086589134938086841 1754496064941851203565131)
            ·
              refine ⟨2631744097412776805347697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754496064941851203565131 2631744097412776805347697)
              ·
                refine ⟨1973808073059582604010773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631744097412776805347697 1973808073059582604010773)
                ·
                  refine ⟨92522253424667934563005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1973808073059582604010773 92522253424667934563005)
                  ·
                    rfl

theorem cell23_1621678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_1621678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621678 prefixEnd_1621678 := by exact prefixLift 1621678
  have htrace : WordTrace (prefixWord ++ tailWord_1621678) baseStart_1621678 baseEnd_1621678 := by
    simpa [prefixWord, tailWord_1621678, baseEnd_1621678] using wordTrace_append hprefix tailTrace_1621678
  have hstable : (prefixWord ++ tailWord_1621678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621678).length < 2 ^ (prefixWord ++ tailWord_1621678).sum := by decide
  have hdescent : baseEnd_1621678 < baseStart_1621678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621731 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1621731 : Nat := 118140960795 + 1621731 * 2 ^ 59
def prefixEnd_1621731 : Nat := 4983230072969 + 3 ^ 40 * 1621731 * 2
def baseEnd_1621731 : Nat := 832727495296699703704301

theorem tailTrace_1621731 : CollatzResearch.WordTrace tailWord_1621731 prefixEnd_1621731 832727495296699703704301 := by
  unfold tailWord_1621731
  simp only [CollatzResearch.WordTrace]
  refine ⟨59149388887753031449233047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39432925925168687632822031 59149388887753031449233047)
  ·
    refine ⟨88724083331629547173849571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59149388887753031449233047 88724083331629547173849571)
    ·
      refine ⟨133086124997444320760774357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88724083331629547173849571 133086124997444320760774357)
      ·
        refine ⟨3119206054627601267830649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 133086124997444320760774357 3119206054627601267830649)
        ·
          refine ⟨2339404540970700950872987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119206054627601267830649 2339404540970700950872987)
          ·
            refine ⟨3509106811456051426309481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339404540970700950872987 3509106811456051426309481)
            ·
              refine ⟨2631830108592038569732111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509106811456051426309481 2631830108592038569732111)
              ·
                refine ⟨3947745162888057854598167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631830108592038569732111 3947745162888057854598167)
                ·
                  refine ⟨5921617744332086781897251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947745162888057854598167 5921617744332086781897251)
                  ·
                    refine ⟨8882426616498130172845877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921617744332086781897251 8882426616498130172845877)
                    ·
                      refine ⟨832727495296699703704301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8882426616498130172845877 832727495296699703704301)
                      ·
                        rfl

theorem cell23_1621731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1621731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621731 prefixEnd_1621731 := by exact prefixLift 1621731
  have htrace : WordTrace (prefixWord ++ tailWord_1621731) baseStart_1621731 baseEnd_1621731 := by
    simpa [prefixWord, tailWord_1621731, baseEnd_1621731] using wordTrace_append hprefix tailTrace_1621731
  have hstable : (prefixWord ++ tailWord_1621731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621731).length < 2 ^ (prefixWord ++ tailWord_1621731).sum := by decide
  have hdescent : baseEnd_1621731 < baseStart_1621731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621748 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1621748 : Nat := 118140960795 + 1621748 * 2 ^ 59
def prefixEnd_1621748 : Nat := 4983230072969 + 3 ^ 40 * 1621748 * 2
def baseEnd_1621748 : Nat := 832736224467826137191723

theorem tailTrace_1621748 : CollatzResearch.WordTrace tailWord_1621748 prefixEnd_1621748 832736224467826137191723 := by
  unfold tailWord_1621748
  simp only [CollatzResearch.WordTrace]
  refine ⟨29575004464345721676300949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39433339285794295568401265 29575004464345721676300949)
  ·
    refine ⟨1386328334266205703576607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29575004464345721676300949 1386328334266205703576607)
    ·
      refine ⟨2079492501399308555364911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386328334266205703576607 2079492501399308555364911)
      ·
        refine ⟨3119238752098962833047367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079492501399308555364911 3119238752098962833047367)
        ·
          refine ⟨4678858128148444249571051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119238752098962833047367 4678858128148444249571051)
          ·
            refine ⟨7018287192222666374356577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678858128148444249571051 7018287192222666374356577)
            ·
              refine ⟨5263715394166999780767433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7018287192222666374356577 5263715394166999780767433)
              ·
                refine ⟨3947786545625249835575575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263715394166999780767433 3947786545625249835575575)
                ·
                  refine ⟨5921679818437874753363363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947786545625249835575575 5921679818437874753363363)
                  ·
                    refine ⟨8882519727656812130045045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921679818437874753363363 8882519727656812130045045)
                    ·
                      refine ⟨832736224467826137191723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8882519727656812130045045 832736224467826137191723)
                      ·
                        rfl

theorem cell23_1621748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1621748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621748 prefixEnd_1621748 := by exact prefixLift 1621748
  have htrace : WordTrace (prefixWord ++ tailWord_1621748) baseStart_1621748 baseEnd_1621748 := by
    simpa [prefixWord, tailWord_1621748, baseEnd_1621748] using wordTrace_append hprefix tailTrace_1621748
  have hstable : (prefixWord ++ tailWord_1621748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621748).length < 2 ^ (prefixWord ++ tailWord_1621748).sum := by decide
  have hdescent : baseEnd_1621748 < baseStart_1621748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621754 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2]
def baseStart_1621754 : Nat := 118140960795 + 1621754 * 2 ^ 59
def prefixEnd_1621754 : Nat := 4983230072969 + 3 ^ 40 * 1621754 * 2
def baseEnd_1621754 : Nat := 832739305351753113716695

theorem tailTrace_1621754 : CollatzResearch.WordTrace tailWord_1621754 prefixEnd_1621754 832739305351753113716695 := by
  unfold tailWord_1621754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787556941667426594330079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39433485177779804251546877 14787556941667426594330079)
  ·
    refine ⟨22181335412501139891495119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14787556941667426594330079 22181335412501139891495119)
    ·
      refine ⟨33272003118751709837242679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22181335412501139891495119 33272003118751709837242679)
      ·
        refine ⟨49908004678127564755864019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33272003118751709837242679 49908004678127564755864019)
        ·
          refine ⟨74862007017191347133796029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49908004678127564755864019 74862007017191347133796029)
          ·
            refine ⟨28073252631446755175173511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74862007017191347133796029 28073252631446755175173511)
            ·
              refine ⟨42109878947170132762760267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28073252631446755175173511 42109878947170132762760267)
              ·
                refine ⟨63164818420755199144140401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42109878947170132762760267 63164818420755199144140401)
                ·
                  refine ⟨47373613815566399358105301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63164818420755199144140401 47373613815566399358105301)
                  ·
                    refine ⟨1110319073802337484955593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47373613815566399358105301 1110319073802337484955593)
                    ·
                      refine ⟨832739305351753113716695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110319073802337484955593 832739305351753113716695)
                      ·
                        rfl

theorem cell23_1621754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_1621754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621754 prefixEnd_1621754 := by exact prefixLift 1621754
  have htrace : WordTrace (prefixWord ++ tailWord_1621754) baseStart_1621754 baseEnd_1621754 := by
    simpa [prefixWord, tailWord_1621754, baseEnd_1621754] using wordTrace_append hprefix tailTrace_1621754
  have hstable : (prefixWord ++ tailWord_1621754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621754).length < 2 ^ (prefixWord ++ tailWord_1621754).sum := by decide
  have hdescent : baseEnd_1621754 < baseStart_1621754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621757 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1621757 : Nat := 118140960795 + 1621757 * 2 ^ 59
def prefixEnd_1621757 : Nat := 4983230072969 + 3 ^ 40 * 1621757 * 2
def baseEnd_1621757 : Nat := 832740845793716601979181

theorem tailTrace_1621757 : CollatzResearch.WordTrace tailWord_1621757 prefixEnd_1621757 832740845793716601979181 := by
  unfold tailWord_1621757
  simp only [CollatzResearch.WordTrace]
  refine ⟨59150337185658837889679525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39433558123772558593119683 59150337185658837889679525)
  ·
    refine ⟨11090688222311032104314911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59150337185658837889679525 11090688222311032104314911)
    ·
      refine ⟨16636032333466548156472367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11090688222311032104314911 16636032333466548156472367)
      ·
        refine ⟨24954048500199822234708551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16636032333466548156472367 24954048500199822234708551)
        ·
          refine ⟨37431072750299733352062827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24954048500199822234708551 37431072750299733352062827)
          ·
            refine ⟨56146609125449600028094241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37431072750299733352062827 56146609125449600028094241)
            ·
              refine ⟨42109956844087200021070681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56146609125449600028094241 42109956844087200021070681)
              ·
                refine ⟨31582467633065400015803011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42109956844087200021070681 31582467633065400015803011)
                ·
                  refine ⟨47373701449598100023704517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31582467633065400015803011 47373701449598100023704517)
                  ·
                    refine ⟨8882569021799643754444597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47373701449598100023704517 8882569021799643754444597)
                    ·
                      refine ⟨832740845793716601979181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8882569021799643754444597 832740845793716601979181)
                      ·
                        rfl

theorem cell23_1621757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1621757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621757 prefixEnd_1621757 := by exact prefixLift 1621757
  have htrace : WordTrace (prefixWord ++ tailWord_1621757) baseStart_1621757 baseEnd_1621757 := by
    simpa [prefixWord, tailWord_1621757, baseEnd_1621757] using wordTrace_append hprefix tailTrace_1621757
  have hstable : (prefixWord ++ tailWord_1621757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621757).length < 2 ^ (prefixWord ++ tailWord_1621757).sum := by decide
  have hdescent : baseEnd_1621757 < baseStart_1621757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621766 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1621766 : Nat := 118140960795 + 1621766 * 2 ^ 59
def prefixEnd_1621766 : Nat := 4983230072969 + 3 ^ 40 * 1621766 * 2
def baseEnd_1621766 : Nat := 832745467119607066766641

theorem tailTrace_1621766 : CollatzResearch.WordTrace tailWord_1621766 prefixEnd_1621766 832745467119607066766641 := by
  unfold tailWord_1621766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848458295082069763336161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39433776961750821617838101 1848458295082069763336161)
  ·
    refine ⟨1386343721311552322502121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1848458295082069763336161 1386343721311552322502121)
    ·
      refine ⟨1039757790983664241876591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1386343721311552322502121 1039757790983664241876591)
      ·
        refine ⟨1559636686475496362814887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039757790983664241876591 1559636686475496362814887)
        ·
          refine ⟨2339455029713244544222331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559636686475496362814887 2339455029713244544222331)
          ·
            refine ⟨3509182544569866816333497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339455029713244544222331 3509182544569866816333497)
            ·
              refine ⟨2631886908427400112250123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509182544569866816333497 2631886908427400112250123)
              ·
                refine ⟨3947830362641100168375185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631886908427400112250123 3947830362641100168375185)
                ·
                  refine ⟨2960872771980825126281389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947830362641100168375185 2960872771980825126281389)
                  ·
                    refine ⟨1110327289492809422355521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960872771980825126281389 1110327289492809422355521)
                    ·
                      refine ⟨832745467119607066766641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110327289492809422355521 832745467119607066766641)
                      ·
                        rfl

theorem cell23_1621766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1621766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621766 prefixEnd_1621766 := by exact prefixLift 1621766
  have htrace : WordTrace (prefixWord ++ tailWord_1621766) baseStart_1621766 baseEnd_1621766 := by
    simpa [prefixWord, tailWord_1621766, baseEnd_1621766] using wordTrace_append hprefix tailTrace_1621766
  have hstable : (prefixWord ++ tailWord_1621766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621766).length < 2 ^ (prefixWord ++ tailWord_1621766).sum := by decide
  have hdescent : baseEnd_1621766 < baseStart_1621766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621777 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 4, 6]
def baseStart_1621777 : Nat := 118140960795 + 1621777 * 2 ^ 59
def prefixEnd_1621777 : Nat := 4983230072969 + 3 ^ 40 * 1621777 * 2
def baseEnd_1621777 : Nat := 277583705135602174576363

theorem tailTrace_1621777 : CollatzResearch.WordTrace tailWord_1621777 prefixEnd_1621777 277583705135602174576363 := by
  unfold tailWord_1621777
  simp only [CollatzResearch.WordTrace]
  refine ⟨59151066645586381305407585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39434044430390920870271723 59151066645586381305407585)
  ·
    refine ⟨44363299984189785979055689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59151066645586381305407585 44363299984189785979055689)
    ·
      refine ⟨33272474988142339484291767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44363299984189785979055689 33272474988142339484291767)
      ·
        refine ⟨49908712482213509226437651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33272474988142339484291767 49908712482213509226437651)
        ·
          refine ⟨74863068723320263839656477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49908712482213509226437651 74863068723320263839656477)
          ·
            refine ⟨28073650771245098939871179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74863068723320263839656477 28073650771245098939871179)
            ·
              refine ⟨42110476156867648409806769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28073650771245098939871179 42110476156867648409806769)
              ·
                refine ⟨31582857117650736307355077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42110476156867648409806769 31582857117650736307355077)
                ·
                  refine ⟨5921785709559513057629077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31582857117650736307355077 5921785709559513057629077)
                  ·
                    refine ⟨277583705135602174576363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5921785709559513057629077 277583705135602174576363)
                    ·
                      rfl

theorem cell23_1621777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_1621777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621777 prefixEnd_1621777 := by exact prefixLift 1621777
  have htrace : WordTrace (prefixWord ++ tailWord_1621777) baseStart_1621777 baseEnd_1621777 := by
    simpa [prefixWord, tailWord_1621777, baseEnd_1621777] using wordTrace_append hprefix tailTrace_1621777
  have hstable : (prefixWord ++ tailWord_1621777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621777).length < 2 ^ (prefixWord ++ tailWord_1621777).sum := by decide
  have hdescent : baseEnd_1621777 < baseStart_1621777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621778 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1621778 : Nat := 118140960795 + 1621778 * 2 ^ 59
def prefixEnd_1621778 : Nat := 4983230072969 + 3 ^ 40 * 1621778 * 2
def baseEnd_1621778 : Nat := 832751628887461019816585

theorem tailTrace_1621778 : CollatzResearch.WordTrace tailWord_1621778 prefixEnd_1621778 832751628887461019816585 := by
  unfold tailWord_1621778
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787775779645689619048497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39434068745721838984129325 14787775779645689619048497)
  ·
    refine ⟨11090831834734267214286373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14787775779645689619048497 11090831834734267214286373)
    ·
      refine ⟨2079530969012675102678695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11090831834734267214286373 2079530969012675102678695)
      ·
        refine ⟨3119296453519012654018043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079530969012675102678695 3119296453519012654018043)
        ·
          refine ⟨4678944680278518981027065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119296453519012654018043 4678944680278518981027065)
          ·
            refine ⟨3509208510208889235770299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4678944680278518981027065 3509208510208889235770299)
            ·
              refine ⟨5263812765313333853655449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3509208510208889235770299 5263812765313333853655449)
              ·
                refine ⟨3947859573985000390241587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263812765313333853655449 3947859573985000390241587)
                ·
                  refine ⟨5921789360977500585362381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947859573985000390241587 5921789360977500585362381)
                  ·
                    refine ⟨2220671010366562719510893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5921789360977500585362381 2220671010366562719510893)
                    ·
                      refine ⟨832751628887461019816585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220671010366562719510893 832751628887461019816585)
                      ·
                        rfl

theorem cell23_1621778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1621778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621778 prefixEnd_1621778 := by exact prefixLift 1621778
  have htrace : WordTrace (prefixWord ++ tailWord_1621778) baseStart_1621778 baseEnd_1621778 := by
    simpa [prefixWord, tailWord_1621778, baseEnd_1621778] using wordTrace_append hprefix tailTrace_1621778
  have hstable : (prefixWord ++ tailWord_1621778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621778).length < 2 ^ (prefixWord ++ tailWord_1621778).sum := by decide
  have hdescent : baseEnd_1621778 < baseStart_1621778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621794 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1621794 : Nat := 118140960795 + 1621794 * 2 ^ 59
def prefixEnd_1621794 : Nat := 4983230072969 + 3 ^ 40 * 1621794 * 2
def baseEnd_1621794 : Nat := 277586614859310985738837

theorem tailTrace_1621794 : CollatzResearch.WordTrace tailWord_1621794 prefixEnd_1621794 277586614859310985738837 := by
  unfold tailWord_1621794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787921671631198302194109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39434457791016528805850957 14787921671631198302194109)
  ·
    refine ⟨5545470626861699363322791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14787921671631198302194109 5545470626861699363322791)
    ·
      refine ⟨8318205940292549044984187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5545470626861699363322791 8318205940292549044984187)
      ·
        refine ⟨12477308910438823567476281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8318205940292549044984187 12477308910438823567476281)
        ·
          refine ⟨9357981682829117675607211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12477308910438823567476281 9357981682829117675607211)
          ·
            refine ⟨14036972524243676513410817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357981682829117675607211 14036972524243676513410817)
            ·
              refine ⟨10527729393182757385058113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14036972524243676513410817 10527729393182757385058113)
              ·
                refine ⟨7895797044887068038793585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10527729393182757385058113 7895797044887068038793585)
                ·
                  refine ⟨5921847783665301029095189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7895797044887068038793585 5921847783665301029095189)
                  ·
                    refine ⟨277586614859310985738837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5921847783665301029095189 277586614859310985738837)
                    ·
                      rfl

theorem cell23_1621794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1621794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621794 prefixEnd_1621794 := by exact prefixLift 1621794
  have htrace : WordTrace (prefixWord ++ tailWord_1621794) baseStart_1621794 baseEnd_1621794 := by
    simpa [prefixWord, tailWord_1621794, baseEnd_1621794] using wordTrace_append hprefix tailTrace_1621794
  have hstable : (prefixWord ++ tailWord_1621794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621794).length < 2 ^ (prefixWord ++ tailWord_1621794).sum := by decide
  have hdescent : baseEnd_1621794 < baseStart_1621794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621804 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_1621804 : Nat := 118140960795 + 1621804 * 2 ^ 59
def prefixEnd_1621804 : Nat := 4983230072969 + 3 ^ 40 * 1621804 * 2
def baseEnd_1621804 : Nat := 832764979384477918091465

theorem tailTrace_1621804 : CollatzResearch.WordTrace tailWord_1621804 prefixEnd_1621804 832764979384477918091465 := by
  unfold tailWord_1621804
  simp only [CollatzResearch.WordTrace]
  refine ⟨29576025708244282458320233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39434700944325709944426977 29576025708244282458320233)
  ·
    refine ⟨22182019281183211843740175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29576025708244282458320233 22182019281183211843740175)
    ·
      refine ⟨33273028921774817765610263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22182019281183211843740175 33273028921774817765610263)
      ·
        refine ⟨49909543382662226648415395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33273028921774817765610263 49909543382662226648415395)
        ·
          refine ⟨74864315073993339972623093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49909543382662226648415395 74864315073993339972623093)
          ·
            refine ⟨7018529538186875622433415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74864315073993339972623093 7018529538186875622433415)
            ·
              refine ⟨10527794307280313433650123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018529538186875622433415 10527794307280313433650123)
              ·
                refine ⟨15791691460920470150475185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527794307280313433650123 15791691460920470150475185)
                ·
                  refine ⟨11843768595690352612856389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15791691460920470150475185 11843768595690352612856389)
                  ·
                    refine ⟨2220706611691941114910573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11843768595690352612856389 2220706611691941114910573)
                    ·
                      refine ⟨832764979384477918091465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220706611691941114910573 832764979384477918091465)
                      ·
                        rfl

theorem cell23_1621804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_1621804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621804 prefixEnd_1621804 := by exact prefixLift 1621804
  have htrace : WordTrace (prefixWord ++ tailWord_1621804) baseStart_1621804 baseEnd_1621804 := by
    simpa [prefixWord, tailWord_1621804, baseEnd_1621804] using wordTrace_append hprefix tailTrace_1621804
  have hstable : (prefixWord ++ tailWord_1621804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621804).length < 2 ^ (prefixWord ++ tailWord_1621804).sum := by decide
  have hdescent : baseEnd_1621804 < baseStart_1621804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621818 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2]
def baseStart_1621818 : Nat := 118140960795 + 1621818 * 2 ^ 59
def prefixEnd_1621818 : Nat := 4983230072969 + 3 ^ 40 * 1621818 * 2
def baseEnd_1621818 : Nat := 832772168113640863316401

theorem tailTrace_1621818 : CollatzResearch.WordTrace tailWord_1621818 prefixEnd_1621818 832772168113640863316401 := by
  unfold tailWord_1621818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788140509609461326912527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39435041358958563538433405 14788140509609461326912527)
  ·
    refine ⟨22182210764414191990368791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788140509609461326912527 22182210764414191990368791)
    ·
      refine ⟨33273316146621287985553187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22182210764414191990368791 33273316146621287985553187)
      ·
        refine ⟨49909974219931931978329781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33273316146621287985553187 49909974219931931978329781)
        ·
          refine ⟨4679060083118618622968417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49909974219931931978329781 4679060083118618622968417)
          ·
            refine ⟨3509295062338963967226313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4679060083118618622968417 3509295062338963967226313)
            ·
              refine ⟨2631971296754222975419735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509295062338963967226313 2631971296754222975419735)
              ·
                refine ⟨3947956945131334463129603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631971296754222975419735 3947956945131334463129603)
                ·
                  refine ⟨5921935417697001694694405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947956945131334463129603 5921935417697001694694405)
                  ·
                    refine ⟨1110362890818187817755201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921935417697001694694405 1110362890818187817755201)
                    ·
                      refine ⟨832772168113640863316401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110362890818187817755201 832772168113640863316401)
                      ·
                        rfl

theorem cell23_1621818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_1621818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621818 prefixEnd_1621818 := by exact prefixLift 1621818
  have htrace : WordTrace (prefixWord ++ tailWord_1621818) baseStart_1621818 baseEnd_1621818 := by
    simpa [prefixWord, tailWord_1621818, baseEnd_1621818] using wordTrace_append hprefix tailTrace_1621818
  have hstable : (prefixWord ++ tailWord_1621818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621818).length < 2 ^ (prefixWord ++ tailWord_1621818).sum := by decide
  have hdescent : baseEnd_1621818 < baseStart_1621818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621834 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_1621834 : Nat := 118140960795 + 1621834 * 2 ^ 59
def prefixEnd_1621834 : Nat := 4983230072969 + 3 ^ 40 * 1621834 * 2
def baseEnd_1621834 : Nat := 832780383804112800716327

theorem tailTrace_1621834 : CollatzResearch.WordTrace tailWord_1621834 prefixEnd_1621834 832780383804112800716327 := by
  unfold tailWord_1621834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788286401594970010058139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39435430404253253360155037 14788286401594970010058139)
  ·
    refine ⟨22182429602392455015087209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788286401594970010058139 22182429602392455015087209)
    ·
      refine ⟨16636822201794341261315407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22182429602392455015087209 16636822201794341261315407)
      ·
        refine ⟨24955233302691511891973111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16636822201794341261315407 24955233302691511891973111)
        ·
          refine ⟨37432849954037267837959667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24955233302691511891973111 37432849954037267837959667)
          ·
            refine ⟨56149274931055901756939501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37432849954037267837959667 56149274931055901756939501)
            ·
              refine ⟨21055978099145963158852313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56149274931055901756939501 21055978099145963158852313)
              ·
                refine ⟨15791983574359472369139235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21055978099145963158852313 15791983574359472369139235)
                ·
                  refine ⟨23687975361539208553708853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15791983574359472369139235 23687975361539208553708853)
                  ·
                    refine ⟨2220747690144300801910205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23687975361539208553708853 2220747690144300801910205)
                    ·
                      refine ⟨832780383804112800716327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220747690144300801910205 832780383804112800716327)
                      ·
                        rfl

theorem cell23_1621834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_1621834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621834 prefixEnd_1621834 := by exact prefixLift 1621834
  have htrace : WordTrace (prefixWord ++ tailWord_1621834) baseStart_1621834 baseEnd_1621834 := by
    simpa [prefixWord, tailWord_1621834, baseEnd_1621834] using wordTrace_append hprefix tailTrace_1621834
  have hstable : (prefixWord ++ tailWord_1621834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621834).length < 2 ^ (prefixWord ++ tailWord_1621834).sum := by decide
  have hdescent : baseEnd_1621834 < baseStart_1621834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621841 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 5]
def baseStart_1621841 : Nat := 118140960795 + 1621841 * 2 ^ 59
def prefixEnd_1621841 : Nat := 4983230072969 + 3 ^ 40 * 1621841 * 2
def baseEnd_1621841 : Nat := 92531553129854919258755

theorem tailTrace_1621841 : CollatzResearch.WordTrace tailWord_1621841 prefixEnd_1621841 92531553129854919258755 := by
  unfold tailWord_1621841
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153400917354520235737377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39435600611569680157158251 59153400917354520235737377)
  ·
    refine ⟨44365050688015890176803033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59153400917354520235737377 44365050688015890176803033)
    ·
      refine ⟨33273788016011917632602275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44365050688015890176803033 33273788016011917632602275)
      ·
        refine ⟨49910682024017876448903413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33273788016011917632602275 49910682024017876448903413)
        ·
          refine ⟨4679126439751675917084695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49910682024017876448903413 4679126439751675917084695)
          ·
            refine ⟨7018689659627513875627043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679126439751675917084695 7018689659627513875627043)
            ·
              refine ⟨10528034489441270813440565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018689659627513875627043 10528034489441270813440565)
              ·
                refine ⟨987003233385119138760053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10528034489441270813440565 987003233385119138760053)
                ·
                  refine ⟨92531553129854919258755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987003233385119138760053 92531553129854919258755)
                  ·
                    rfl

theorem cell23_1621841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 5].length) (baseStart_1621841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621841 prefixEnd_1621841 := by exact prefixLift 1621841
  have htrace : WordTrace (prefixWord ++ tailWord_1621841) baseStart_1621841 baseEnd_1621841 := by
    simpa [prefixWord, tailWord_1621841, baseEnd_1621841] using wordTrace_append hprefix tailTrace_1621841
  have hstable : (prefixWord ++ tailWord_1621841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621841).length < 2 ^ (prefixWord ++ tailWord_1621841).sum := by decide
  have hdescent : baseEnd_1621841 < baseStart_1621841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621858 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1621858 : Nat := 118140960795 + 1621858 * 2 ^ 59
def prefixEnd_1621858 : Nat := 4983230072969 + 3 ^ 40 * 1621858 * 2
def baseEnd_1621858 : Nat := 92532523037757856312913

theorem tailTrace_1621858 : CollatzResearch.WordTrace tailWord_1621858 prefixEnd_1621858 92532523037757856312913 := by
  unfold tailWord_1621858
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788505239573233034776557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39436013972195288092737485 14788505239573233034776557)
  ·
    refine ⟨5545689464839962388041209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14788505239573233034776557 5545689464839962388041209)
    ·
      refine ⟨4159267098629971791030907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5545689464839962388041209 4159267098629971791030907)
      ·
        refine ⟨6238900647944957686546361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159267098629971791030907 6238900647944957686546361)
        ·
          refine ⟨4679175485958718264909771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6238900647944957686546361 4679175485958718264909771)
          ·
            refine ⟨7018763228938077397364657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679175485958718264909771 7018763228938077397364657)
            ·
              refine ⟨5264072421703558048023493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7018763228938077397364657 5264072421703558048023493)
              ·
                refine ⟨987013579069417134004405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5264072421703558048023493 987013579069417134004405)
                ·
                  refine ⟨92532523037757856312913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987013579069417134004405 92532523037757856312913)
                  ·
                    rfl

theorem cell23_1621858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1621858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621858 prefixEnd_1621858 := by exact prefixLift 1621858
  have htrace : WordTrace (prefixWord ++ tailWord_1621858) baseStart_1621858 baseEnd_1621858 := by
    simpa [prefixWord, tailWord_1621858, baseEnd_1621858] using wordTrace_append hprefix tailTrace_1621858
  have hstable : (prefixWord ++ tailWord_1621858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621858).length < 2 ^ (prefixWord ++ tailWord_1621858).sum := by decide
  have hdescent : baseEnd_1621858 < baseStart_1621858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621864 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1621864 : Nat := 118140960795 + 1621864 * 2 ^ 59
def prefixEnd_1621864 : Nat := 4983230072969 + 3 ^ 40 * 1621864 * 2
def baseEnd_1621864 : Nat := 832795788223747683341189

theorem tailTrace_1621864 : CollatzResearch.WordTrace tailWord_1621864 prefixEnd_1621864 832795788223747683341189 := by
  unfold tailWord_1621864
  simp only [CollatzResearch.WordTrace]
  refine ⟨29577119898135597581912323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39436159864180796775883097 29577119898135597581912323)
  ·
    refine ⟨44365679847203396372868485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29577119898135597581912323 44365679847203396372868485)
    ·
      refine ⟨8318564971350636819912841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44365679847203396372868485 8318564971350636819912841)
      ·
        refine ⟨6238923728512977614934631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8318564971350636819912841 6238923728512977614934631)
        ·
          refine ⟨9358385592769466422401947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6238923728512977614934631 9358385592769466422401947)
          ·
            refine ⟨14037578389154199633602921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358385592769466422401947 14037578389154199633602921)
            ·
              refine ⟨10528183791865649725202191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14037578389154199633602921 10528183791865649725202191)
              ·
                refine ⟨15792275687798474587803287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528183791865649725202191 15792275687798474587803287)
                ·
                  refine ⟨23688413531697711881704931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15792275687798474587803287 23688413531697711881704931)
                  ·
                    refine ⟨35532620297546567822557397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23688413531697711881704931 35532620297546567822557397)
                    ·
                      refine ⟨832795788223747683341189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35532620297546567822557397 832795788223747683341189)
                      ·
                        rfl

theorem cell23_1621864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1621864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621864 prefixEnd_1621864 := by exact prefixLift 1621864
  have htrace : WordTrace (prefixWord ++ tailWord_1621864) baseStart_1621864 baseEnd_1621864 := by
    simpa [prefixWord, tailWord_1621864, baseEnd_1621864] using wordTrace_append hprefix tailTrace_1621864
  have hstable : (prefixWord ++ tailWord_1621864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621864).length < 2 ^ (prefixWord ++ tailWord_1621864).sum := by decide
  have hdescent : baseEnd_1621864 < baseStart_1621864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621908 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1621908 : Nat := 118140960795 + 1621908 * 2 ^ 59
def prefixEnd_1621908 : Nat := 4983230072969 + 3 ^ 40 * 1621908 * 2
def baseEnd_1621908 : Nat := 832818381372545511190987

theorem tailTrace_1621908 : CollatzResearch.WordTrace tailWord_1621908 prefixEnd_1621908 832818381372545511190987 := by
  unfold tailWord_1621908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29577922304055895339213189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39437229738741193785617585 29577922304055895339213189)
  ·
    refine ⟨5545860432010480376102473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29577922304055895339213189 5545860432010480376102473)
    ·
      refine ⟨4159395324007860282076855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5545860432010480376102473 4159395324007860282076855)
      ·
        refine ⟨6239092986011790423115283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159395324007860282076855 6239092986011790423115283)
        ·
          refine ⟨9358639479017685634672925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6239092986011790423115283 9358639479017685634672925)
          ·
            refine ⟨3509489804631632113002347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9358639479017685634672925 3509489804631632113002347)
            ·
              refine ⟨5264234706947448169503521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3509489804631632113002347 5264234706947448169503521)
              ·
                refine ⟨3948176030210586127127641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5264234706947448169503521 3948176030210586127127641)
                ·
                  refine ⟨2961132022657939595345731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3948176030210586127127641 2961132022657939595345731)
                  ·
                    refine ⟨4441698033986909393018597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2961132022657939595345731 4441698033986909393018597)
                    ·
                      refine ⟨832818381372545511190987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4441698033986909393018597 832818381372545511190987)
                      ·
                        rfl

theorem cell23_1621908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1621908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621908 prefixEnd_1621908 := by exact prefixLift 1621908
  have htrace : WordTrace (prefixWord ++ tailWord_1621908) baseStart_1621908 baseEnd_1621908 := by
    simpa [prefixWord, tailWord_1621908, baseEnd_1621908] using wordTrace_append hprefix tailTrace_1621908
  have hstable : (prefixWord ++ tailWord_1621908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621908).length < 2 ^ (prefixWord ++ tailWord_1621908).sum := by decide
  have hdescent : baseEnd_1621908 < baseStart_1621908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621911 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1621911 : Nat := 118140960795 + 1621911 * 2 ^ 59
def prefixEnd_1621911 : Nat := 4983230072969 + 3 ^ 40 * 1621911 * 2
def baseEnd_1621911 : Nat := 832819921814508999453473

theorem tailTrace_1621911 : CollatzResearch.WordTrace tailWord_1621911 prefixEnd_1621911 832819921814508999453473 := by
  unfold tailWord_1621911
  simp only [CollatzResearch.WordTrace]
  refine ⟨59155954027100922190785587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39437302684733948127190391 59155954027100922190785587)
  ·
    refine ⟨88733931040651383286178381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59155954027100922190785587 88733931040651383286178381)
    ·
      refine ⟨33275224140244268732316893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88733931040651383286178381 33275224140244268732316893)
      ·
        refine ⟨12478209052591600774618835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33275224140244268732316893 12478209052591600774618835)
        ·
          refine ⟨18717313578887401161928253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478209052591600774618835 18717313578887401161928253)
          ·
            refine ⟨7018992592082775435723095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18717313578887401161928253 7018992592082775435723095)
            ·
              refine ⟨10528488888124163153584643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018992592082775435723095 10528488888124163153584643)
              ·
                refine ⟨15792733332186244730376965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528488888124163153584643 15792733332186244730376965)
                ·
                  refine ⟨2961137499784920886945681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15792733332186244730376965 2961137499784920886945681)
                  ·
                    refine ⟨2220853124838690665209261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2961137499784920886945681 2220853124838690665209261)
                    ·
                      refine ⟨832819921814508999453473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220853124838690665209261 832819921814508999453473)
                      ·
                        rfl

theorem cell23_1621911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1621911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621911 prefixEnd_1621911 := by exact prefixLift 1621911
  have htrace : WordTrace (prefixWord ++ tailWord_1621911) baseStart_1621911 baseEnd_1621911 := by
    simpa [prefixWord, tailWord_1621911, baseEnd_1621911] using wordTrace_append hprefix tailTrace_1621911
  have hstable : (prefixWord ++ tailWord_1621911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621911).length < 2 ^ (prefixWord ++ tailWord_1621911).sum := by decide
  have hdescent : baseEnd_1621911 < baseStart_1621911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621968 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 2, 3, 2]
def baseStart_1621968 : Nat := 118140960795 + 1621968 * 2 ^ 59
def prefixEnd_1621968 : Nat := 4983230072969 + 3 ^ 40 * 1621968 * 2
def baseEnd_1621968 : Nat := 832849190211815276440711

theorem tailTrace_1621968 : CollatzResearch.WordTrace tailWord_1621968 prefixEnd_1621968 832849190211815276440711 := by
  unfold tailWord_1621968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29579016493947210462805279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39438688658596280617073705 29579016493947210462805279)
  ·
    refine ⟨44368524740920815694207919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29579016493947210462805279 44368524740920815694207919)
    ·
      refine ⟨66552787111381223541311879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44368524740920815694207919 66552787111381223541311879)
      ·
        refine ⟨99829180667071835311967819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66552787111381223541311879 99829180667071835311967819)
        ·
          refine ⟨149743771000607752967951729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99829180667071835311967819 149743771000607752967951729)
          ·
            refine ⟨112307828250455814725963797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149743771000607752967951729 112307828250455814725963797)
            ·
              refine ⟨5264429449240116315279553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112307828250455814725963797 5264429449240116315279553)
              ·
                refine ⟨3948322086930087236459665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5264429449240116315279553 3948322086930087236459665)
                ·
                  refine ⟨2961241565197565427344749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3948322086930087236459665 2961241565197565427344749)
                  ·
                    refine ⟨1110465586949087035254281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961241565197565427344749 1110465586949087035254281)
                    ·
                      refine ⟨832849190211815276440711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110465586949087035254281 832849190211815276440711)
                      ·
                        rfl

theorem cell23_1621968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 3, 2].length) (baseStart_1621968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621968 prefixEnd_1621968 := by exact prefixLift 1621968
  have htrace : WordTrace (prefixWord ++ tailWord_1621968) baseStart_1621968 baseEnd_1621968 := by
    simpa [prefixWord, tailWord_1621968, baseEnd_1621968] using wordTrace_append hprefix tailTrace_1621968
  have hstable : (prefixWord ++ tailWord_1621968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621968).length < 2 ^ (prefixWord ++ tailWord_1621968).sum := by decide
  have hdescent : baseEnd_1621968 < baseStart_1621968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621975 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 1, 1, 3]
def baseStart_1621975 : Nat := 118140960795 + 1621975 * 2 ^ 59
def prefixEnd_1621975 : Nat := 4983230072969 + 3 ^ 40 * 1621975 * 2
def baseEnd_1621975 : Nat := 832852784576396749053179

theorem tailTrace_1621975 : CollatzResearch.WordTrace tailWord_1621975 prefixEnd_1621975 832852784576396749053179 := by
  unfold tailWord_1621975
  simp only [CollatzResearch.WordTrace]
  refine ⟨59158288298869061121115379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39438858865912707414076919 59158288298869061121115379)
  ·
    refine ⟨88737432448303591681673069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59158288298869061121115379 88737432448303591681673069)
    ·
      refine ⟨33276537168113846880627401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88737432448303591681673069 33276537168113846880627401)
      ·
        refine ⟨24957402876085385160470551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33276537168113846880627401 24957402876085385160470551)
        ·
          refine ⟨37436104314128077740705827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24957402876085385160470551 37436104314128077740705827)
          ·
            refine ⟨56154156471192116611058741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37436104314128077740705827 56154156471192116611058741)
            ·
              refine ⟨5264452169174260932286757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56154156471192116611058741 5264452169174260932286757)
              ·
                refine ⟨987084781720173924803767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5264452169174260932286757 987084781720173924803767)
                ·
                  refine ⟨1480627172580260887205651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987084781720173924803767 1480627172580260887205651)
                  ·
                    refine ⟨2220940758870391330808477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1480627172580260887205651 2220940758870391330808477)
                    ·
                      refine ⟨832852784576396749053179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2220940758870391330808477 832852784576396749053179)
                      ·
                        rfl

theorem cell23_1621975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_1621975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621975 prefixEnd_1621975 := by exact prefixLift 1621975
  have htrace : WordTrace (prefixWord ++ tailWord_1621975) baseStart_1621975 baseEnd_1621975 := by
    simpa [prefixWord, tailWord_1621975, baseEnd_1621975] using wordTrace_append hprefix tailTrace_1621975
  have hstable : (prefixWord ++ tailWord_1621975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621975).length < 2 ^ (prefixWord ++ tailWord_1621975).sum := by decide
  have hdescent : baseEnd_1621975 < baseStart_1621975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621998 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1621998 : Nat := 118140960795 + 1621998 * 2 ^ 59
def prefixEnd_1621998 : Nat := 4983230072969 + 3 ^ 40 * 1621998 * 2
def baseEnd_1621998 : Nat := 832864594631450159065573

theorem tailTrace_1621998 : CollatzResearch.WordTrace tailWord_1621998 prefixEnd_1621998 832864594631450159065573 := by
  unfold tailWord_1621998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7394890897223217006150331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39439418118523824032801765 7394890897223217006150331)
  ·
    refine ⟨11092336345834825509225497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7394890897223217006150331 11092336345834825509225497)
    ·
      refine ⟨8319252259376119131919123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11092336345834825509225497 8319252259376119131919123)
      ·
        refine ⟨12478878389064178697878685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8319252259376119131919123 12478878389064178697878685)
        ·
          refine ⟨4679579395899067011704507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12478878389064178697878685 4679579395899067011704507)
          ·
            refine ⟨7019369093848600517556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679579395899067011704507 7019369093848600517556761)
            ·
              refine ⟨5264526820386450388167571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7019369093848600517556761 5264526820386450388167571)
              ·
                refine ⟨7896790230579675582251357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5264526820386450388167571 7896790230579675582251357)
                ·
                  refine ⟨2961296336467378343344259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7896790230579675582251357 2961296336467378343344259)
                  ·
                    refine ⟨4441944504701067515016389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2961296336467378343344259 4441944504701067515016389)
                    ·
                      refine ⟨832864594631450159065573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4441944504701067515016389 832864594631450159065573)
                      ·
                        rfl

theorem cell23_1621998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1621998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1621998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1621998 prefixEnd_1621998 := by exact prefixLift 1621998
  have htrace : WordTrace (prefixWord ++ tailWord_1621998) baseStart_1621998 baseEnd_1621998 := by
    simpa [prefixWord, tailWord_1621998, baseEnd_1621998] using wordTrace_append hprefix tailTrace_1621998
  have hstable : (prefixWord ++ tailWord_1621998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621998).length < 2 ^ (prefixWord ++ tailWord_1621998).sum := by decide
  have hdescent : baseEnd_1621998 < baseStart_1621998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622011 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4]
def baseStart_1622011 : Nat := 118140960795 + 1622011 * 2 ^ 59
def prefixEnd_1622011 : Nat := 4983230072969 + 3 ^ 40 * 1622011 * 2
def baseEnd_1622011 : Nat := 832871269879958608203013

theorem tailTrace_1622011 : CollatzResearch.WordTrace tailWord_1622011 prefixEnd_1622011 832871269879958608203013 := by
  unfold tailWord_1622011
  simp only [CollatzResearch.WordTrace]
  refine ⟨59159601326738639269425887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39439734217825759512950591 59159601326738639269425887)
  ·
    refine ⟨88739401990107958904138831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59159601326738639269425887 88739401990107958904138831)
    ·
      refine ⟨133109102985161938356208247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88739401990107958904138831 133109102985161938356208247)
      ·
        refine ⟨199663654477742907534312371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133109102985161938356208247 199663654477742907534312371)
        ·
          refine ⟨299495481716614361301468557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199663654477742907534312371 299495481716614361301468557)
          ·
            refine ⟨112310805643730385488050709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299495481716614361301468557 112310805643730385488050709)
            ·
              refine ⟨5264569014549861819752377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112310805643730385488050709 5264569014549861819752377)
              ·
                refine ⟨3948426760912396364814283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5264569014549861819752377 3948426760912396364814283)
                ·
                  refine ⟨5922640141368594547221425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948426760912396364814283 5922640141368594547221425)
                  ·
                    refine ⟨4441980106026445910416069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922640141368594547221425 4441980106026445910416069)
                    ·
                      refine ⟨832871269879958608203013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4441980106026445910416069 832871269879958608203013)
                      ·
                        rfl

theorem cell23_1622011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].length) (baseStart_1622011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622011 prefixEnd_1622011 := by exact prefixLift 1622011
  have htrace : WordTrace (prefixWord ++ tailWord_1622011) baseStart_1622011 baseEnd_1622011 := by
    simpa [prefixWord, tailWord_1622011, baseEnd_1622011] using wordTrace_append hprefix tailTrace_1622011
  have hstable : (prefixWord ++ tailWord_1622011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622011).length < 2 ^ (prefixWord ++ tailWord_1622011).sum := by decide
  have hdescent : baseEnd_1622011 < baseStart_1622011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622045 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1622045 : Nat := 118140960795 + 1622045 * 2 ^ 59
def prefixEnd_1622045 : Nat := 4983230072969 + 3 ^ 40 * 1622045 * 2
def baseEnd_1622045 : Nat := 832888728222211475177857

theorem tailTrace_1622045 : CollatzResearch.WordTrace tailWord_1622045 prefixEnd_1622045 832888728222211475177857 := by
  unfold tailWord_1622045
  simp only [CollatzResearch.WordTrace]
  refine ⟨59160841408615463076163589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39440560939076975384109059 59160841408615463076163589)
  ·
    refine ⟨11092657764115399326780673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59160841408615463076163589 11092657764115399326780673)
    ·
      refine ⟨8319493323086549495085505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11092657764115399326780673 8319493323086549495085505)
      ·
        refine ⟨6239619992314912121314129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8319493323086549495085505 6239619992314912121314129)
        ·
          refine ⟨4679714994236184090985597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6239619992314912121314129 4679714994236184090985597)
          ·
            refine ⟨1754893122838569034119599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4679714994236184090985597 1754893122838569034119599)
            ·
              refine ⟨2632339684257853551179399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754893122838569034119599 2632339684257853551179399)
              ·
                refine ⟨3948509526386780326769099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632339684257853551179399 3948509526386780326769099)
                ·
                  refine ⟨5922764289580170490153649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948509526386780326769099 5922764289580170490153649)
                  ·
                    refine ⟨4442073217185127867615237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922764289580170490153649 4442073217185127867615237)
                    ·
                      refine ⟨832888728222211475177857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4442073217185127867615237 832888728222211475177857)
                      ·
                        rfl

theorem cell23_1622045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1622045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622045 prefixEnd_1622045 := by exact prefixLift 1622045
  have htrace : WordTrace (prefixWord ++ tailWord_1622045) baseStart_1622045 baseEnd_1622045 := by
    simpa [prefixWord, tailWord_1622045, baseEnd_1622045] using wordTrace_append hprefix tailTrace_1622045
  have hstable : (prefixWord ++ tailWord_1622045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622045).length < 2 ^ (prefixWord ++ tailWord_1622045).sum := by decide
  have hdescent : baseEnd_1622045 < baseStart_1622045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622052 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1622052 : Nat := 118140960795 + 1622052 * 2 ^ 59
def prefixEnd_1622052 : Nat := 4983230072969 + 3 ^ 40 * 1622052 * 2
def baseEnd_1622052 : Nat := 832892322586792947790325

theorem tailTrace_1622052 : CollatzResearch.WordTrace tailWord_1622052 prefixEnd_1622052 832892322586792947790325 := by
  unfold tailWord_1622052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29580548359795051635834205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39440731146393402181112273 29580548359795051635834205)
  ·
    refine ⟨11092705634923144363437827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29580548359795051635834205 11092705634923144363437827)
    ·
      refine ⟨16639058452384716545156741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11092705634923144363437827 16639058452384716545156741)
      ·
        refine ⟨3119823459822134352216889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16639058452384716545156741 3119823459822134352216889)
        ·
          refine ⟨2339867594866600764162667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119823459822134352216889 2339867594866600764162667)
          ·
            refine ⟨3509801392299901146244001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339867594866600764162667 3509801392299901146244001)
            ·
              refine ⟨2632351044224925859683001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509801392299901146244001 2632351044224925859683001)
              ·
                refine ⟨1974263283168694394762251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632351044224925859683001 1974263283168694394762251)
                ·
                  refine ⟨2961394924753041592143377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974263283168694394762251 2961394924753041592143377)
                  ·
                    refine ⟨2221046193564781194107533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2961394924753041592143377 2221046193564781194107533)
                    ·
                      refine ⟨832892322586792947790325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2221046193564781194107533 832892322586792947790325)
                      ·
                        rfl

theorem cell23_1622052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1622052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622052 prefixEnd_1622052 := by exact prefixLift 1622052
  have htrace : WordTrace (prefixWord ++ tailWord_1622052) baseStart_1622052 baseEnd_1622052 := by
    simpa [prefixWord, tailWord_1622052, baseEnd_1622052] using wordTrace_append hprefix tailTrace_1622052
  have hstable : (prefixWord ++ tailWord_1622052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622052).length < 2 ^ (prefixWord ++ tailWord_1622052).sum := by decide
  have hdescent : baseEnd_1622052 < baseStart_1622052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622088 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_1622088 : Nat := 118140960795 + 1622088 * 2 ^ 59
def prefixEnd_1622088 : Nat := 4983230072969 + 3 ^ 40 * 1622088 * 2
def baseEnd_1622088 : Nat := 832910807890354806940159

theorem tailTrace_1622088 : CollatzResearch.WordTrace tailWord_1622088 prefixEnd_1622088 832910807890354806940159 := by
  unfold tailWord_1622088
  simp only [CollatzResearch.WordTrace]
  refine ⟨29581204873729840709989459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39441606498306454279985945 29581204873729840709989459)
  ·
    refine ⟨44371807310594761064984189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29581204873729840709989459 44371807310594761064984189)
    ·
      refine ⟨16639427741473035399369071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44371807310594761064984189 16639427741473035399369071)
      ·
        refine ⟨24959141612209553099053607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16639427741473035399369071 24959141612209553099053607)
        ·
          refine ⟨37438712418314329648580411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24959141612209553099053607 37438712418314329648580411)
          ·
            refine ⟨56158068627471494472870617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37438712418314329648580411 56158068627471494472870617)
            ·
              refine ⟨42118551470603620854652963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56158068627471494472870617 42118551470603620854652963)
              ·
                refine ⟨63177827205905431281979445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42118551470603620854652963 63177827205905431281979445)
                ·
                  refine ⟨5922921300553634182685573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63177827205905431281979445 5922921300553634182685573)
                  ·
                    refine ⟨1110547743853806409253545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5922921300553634182685573 1110547743853806409253545)
                    ·
                      refine ⟨832910807890354806940159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110547743853806409253545 832910807890354806940159)
                      ·
                        rfl

theorem cell23_1622088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_1622088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622088 prefixEnd_1622088 := by exact prefixLift 1622088
  have htrace : WordTrace (prefixWord ++ tailWord_1622088) baseStart_1622088 baseEnd_1622088 := by
    simpa [prefixWord, tailWord_1622088, baseEnd_1622088] using wordTrace_append hprefix tailTrace_1622088
  have hstable : (prefixWord ++ tailWord_1622088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622088).length < 2 ^ (prefixWord ++ tailWord_1622088).sum := by decide
  have hdescent : baseEnd_1622088 < baseStart_1622088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622091 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 3]
def baseStart_1622091 : Nat := 118140960795 + 1622091 * 2 ^ 59
def prefixEnd_1622091 : Nat := 4983230072969 + 3 ^ 40 * 1622091 * 2
def baseEnd_1622091 : Nat := 832912348332318295202645

theorem tailTrace_1622091 : CollatzResearch.WordTrace tailWord_1622091 prefixEnd_1622091 832912348332318295202645 := by
  unfold tailWord_1622091
  simp only [CollatzResearch.WordTrace]
  refine ⟨59162519166448812932338127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39441679444299208621558751 59162519166448812932338127)
  ·
    refine ⟨88743778749673219398507191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59162519166448812932338127 88743778749673219398507191)
    ·
      refine ⟨133115668124509829097760787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88743778749673219398507191 133115668124509829097760787)
      ·
        refine ⟨199673502186764743646641181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133115668124509829097760787 199673502186764743646641181)
        ·
          refine ⟨74877563320036778867490443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199673502186764743646641181 74877563320036778867490443)
          ·
            refine ⟨112316344980055168301235665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74877563320036778867490443 112316344980055168301235665)
            ·
              refine ⟨84237258735041376225926749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112316344980055168301235665 84237258735041376225926749)
              ·
                refine ⟨31588972025640516084722531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84237258735041376225926749 31588972025640516084722531)
                ·
                  refine ⟨47383458038460774127083797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31588972025640516084722531 47383458038460774127083797)
                  ·
                    refine ⟨2221099595552848787207053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47383458038460774127083797 2221099595552848787207053)
                    ·
                      refine ⟨832912348332318295202645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2221099595552848787207053 832912348332318295202645)
                      ·
                        rfl

theorem cell23_1622091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 6, 3].length) (baseStart_1622091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622091 prefixEnd_1622091 := by exact prefixLift 1622091
  have htrace : WordTrace (prefixWord ++ tailWord_1622091) baseStart_1622091 baseEnd_1622091 := by
    simpa [prefixWord, tailWord_1622091, baseEnd_1622091] using wordTrace_append hprefix tailTrace_1622091
  have hstable : (prefixWord ++ tailWord_1622091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622091).length < 2 ^ (prefixWord ++ tailWord_1622091).sum := by decide
  have hdescent : baseEnd_1622091 < baseStart_1622091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622108 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1622108 : Nat := 118140960795 + 1622108 * 2 ^ 59
def prefixEnd_1622108 : Nat := 4983230072969 + 3 ^ 40 * 1622108 * 2
def baseEnd_1622108 : Nat := 832921077503444728690067

theorem tailTrace_1622108 : CollatzResearch.WordTrace tailWord_1622108 prefixEnd_1622108 832921077503444728690067 := by
  unfold tailWord_1622108
  simp only [CollatzResearch.WordTrace]
  refine ⟨29581569603693612417853489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39442092804924816557137985 29581569603693612417853489)
  ·
    refine ⟨22186177202770209313390117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29581569603693612417853489 22186177202770209313390117)
    ·
      refine ⟨4159908225519414246260647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22186177202770209313390117 4159908225519414246260647)
      ·
        refine ⟨6239862338279121369390971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159908225519414246260647 6239862338279121369390971)
        ·
          refine ⟨9359793507418682054086457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6239862338279121369390971 9359793507418682054086457)
          ·
            refine ⟨7019845130564011540564843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9359793507418682054086457 7019845130564011540564843)
            ·
              refine ⟨10529767695846017310847265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019845130564011540564843 10529767695846017310847265)
              ·
                refine ⟨7897325771884512983135449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10529767695846017310847265 7897325771884512983135449)
                ·
                  refine ⟨5922994328913384737351587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7897325771884512983135449 5922994328913384737351587)
                  ·
                    refine ⟨8884491493370077106027381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922994328913384737351587 8884491493370077106027381)
                    ·
                      refine ⟨832921077503444728690067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8884491493370077106027381 832921077503444728690067)
                      ·
                        rfl

theorem cell23_1622108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1622108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622108 prefixEnd_1622108 := by exact prefixLift 1622108
  have htrace : WordTrace (prefixWord ++ tailWord_1622108) baseStart_1622108 baseEnd_1622108 := by
    simpa [prefixWord, tailWord_1622108, baseEnd_1622108] using wordTrace_append hprefix tailTrace_1622108
  have hstable : (prefixWord ++ tailWord_1622108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622108).length < 2 ^ (prefixWord ++ tailWord_1622108).sum := by decide
  have hdescent : baseEnd_1622108 < baseStart_1622108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622109 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1622109 : Nat := 118140960795 + 1622109 * 2 ^ 59
def prefixEnd_1622109 : Nat := 4983230072969 + 3 ^ 40 * 1622109 * 2
def baseEnd_1622109 : Nat := 832921590984099224777563

theorem tailTrace_1622109 : CollatzResearch.WordTrace tailWord_1622109 prefixEnd_1622109 832921590984099224777563 := by
  unfold tailWord_1622109
  simp only [CollatzResearch.WordTrace]
  refine ⟨59163175680383602006493381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39442117120255734670995587 59163175680383602006493381)
  ·
    refine ⟨11093095440071925376217509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59163175680383602006493381 11093095440071925376217509)
    ·
      refine ⟨2079955395013486008040783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11093095440071925376217509 2079955395013486008040783)
      ·
        refine ⟨3119933092520229012061175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079955395013486008040783 3119933092520229012061175)
        ·
          refine ⟨4679899638780343518091763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119933092520229012061175 4679899638780343518091763)
          ·
            refine ⟨7019849458170515277137645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679899638780343518091763 7019849458170515277137645)
            ·
              refine ⟨2632443546813943228926617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7019849458170515277137645 2632443546813943228926617)
              ·
                refine ⟨1974332660110457421694963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632443546813943228926617 1974332660110457421694963)
                ·
                  refine ⟨2961498990165686132542445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974332660110457421694963 2961498990165686132542445)
                  ·
                    refine ⟨1110562121312132299703417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961498990165686132542445 1110562121312132299703417)
                    ·
                      refine ⟨832921590984099224777563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110562121312132299703417 832921590984099224777563)
                      ·
                        rfl

theorem cell23_1622109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1622109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622109 prefixEnd_1622109 := by exact prefixLift 1622109
  have htrace : WordTrace (prefixWord ++ tailWord_1622109) baseStart_1622109 baseEnd_1622109 := by
    simpa [prefixWord, tailWord_1622109, baseEnd_1622109] using wordTrace_append hprefix tailTrace_1622109
  have hstable : (prefixWord ++ tailWord_1622109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622109).length < 2 ^ (prefixWord ++ tailWord_1622109).sum := by decide
  have hdescent : baseEnd_1622109 < baseStart_1622109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622122 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_1622122 : Nat := 118140960795 + 1622122 * 2 ^ 59
def prefixEnd_1622122 : Nat := 4983230072969 + 3 ^ 40 * 1622122 * 2
def baseEnd_1622122 : Nat := 832928266232607673915003

theorem tailTrace_1622122 : CollatzResearch.WordTrace tailWord_1622122 prefixEnd_1622122 832928266232607673915003 := by
  unfold tailWord_1622122
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790912457334126306679155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39442433219557670151144413 14790912457334126306679155)
  ·
    refine ⟨22186368686001189460018733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14790912457334126306679155 22186368686001189460018733)
    ·
      refine ⟨8319888257250446047507025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22186368686001189460018733 8319888257250446047507025)
      ·
        refine ⟨6239916192937834535630269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8319888257250446047507025 6239916192937834535630269)
        ·
          refine ⟨2339968572351687950861351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6239916192937834535630269 2339968572351687950861351)
          ·
            refine ⟨3509952858527531926292027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339968572351687950861351 3509952858527531926292027)
            ·
              refine ⟨5264929287791297889438041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3509952858527531926292027 5264929287791297889438041)
              ·
                refine ⟨3948696965843473417078531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5264929287791297889438041 3948696965843473417078531)
                ·
                  refine ⟨5923045448765210125617797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948696965843473417078531 5923045448765210125617797)
                  ·
                    refine ⟨1110571021643476898553337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923045448765210125617797 1110571021643476898553337)
                    ·
                      refine ⟨832928266232607673915003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110571021643476898553337 832928266232607673915003)
                      ·
                        rfl

theorem cell23_1622122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_1622122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622122 prefixEnd_1622122 := by exact prefixLift 1622122
  have htrace : WordTrace (prefixWord ++ tailWord_1622122) baseStart_1622122 baseEnd_1622122 := by
    simpa [prefixWord, tailWord_1622122, baseEnd_1622122] using wordTrace_append hprefix tailTrace_1622122
  have hstable : (prefixWord ++ tailWord_1622122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622122).length < 2 ^ (prefixWord ++ tailWord_1622122).sum := by decide
  have hdescent : baseEnd_1622122 < baseStart_1622122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622175 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 2, 5]
def baseStart_1622175 : Nat := 118140960795 + 1622175 * 2 ^ 59
def prefixEnd_1622175 : Nat := 4983230072969 + 3 ^ 40 * 1622175 * 2
def baseEnd_1622175 : Nat := 277651826902431988850753

theorem tailTrace_1622175 : CollatzResearch.WordTrace tailWord_1622175 prefixEnd_1622175 277651826902431988850753 := by
  unfold tailWord_1622175
  simp only [CollatzResearch.WordTrace]
  refine ⟨59165582898144495278395979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39443721932096330185597319 59165582898144495278395979)
  ·
    refine ⟨88748374347216742917593969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59165582898144495278395979 88748374347216742917593969)
    ·
      refine ⟨66561280760412557188195477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88748374347216742917593969 66561280760412557188195477)
      ·
        refine ⟨3120060035644338618196663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66561280760412557188195477 3120060035644338618196663)
        ·
          refine ⟨4680090053466507927294995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120060035644338618196663 4680090053466507927294995)
          ·
            refine ⟨7020135080199761890942493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680090053466507927294995 7020135080199761890942493)
            ·
              refine ⟨2632550655074910709103435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7020135080199761890942493 2632550655074910709103435)
              ·
                refine ⟨3948825982612366063655153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632550655074910709103435 3948825982612366063655153)
                ·
                  refine ⟨2961619486959274547741365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3948825982612366063655153 2961619486959274547741365)
                  ·
                    refine ⟨277651826902431988850753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2961619486959274547741365 277651826902431988850753)
                    ·
                      rfl

theorem cell23_1622175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_1622175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622175 prefixEnd_1622175 := by exact prefixLift 1622175
  have htrace : WordTrace (prefixWord ++ tailWord_1622175) baseStart_1622175 baseEnd_1622175 := by
    simpa [prefixWord, tailWord_1622175, baseEnd_1622175] using wordTrace_append hprefix tailTrace_1622175
  have hstable : (prefixWord ++ tailWord_1622175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622175).length < 2 ^ (prefixWord ++ tailWord_1622175).sum := by decide
  have hdescent : baseEnd_1622175 < baseStart_1622175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622190 : List Nat := [4, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1622190 : Nat := 118140960795 + 1622190 * 2 ^ 59
def prefixEnd_1622190 : Nat := 4983230072969 + 3 ^ 40 * 1622190 * 2
def baseEnd_1622190 : Nat := 832963182917113407864691

theorem tailTrace_1622190 : CollatzResearch.WordTrace tailWord_1622190 prefixEnd_1622190 832963182917113407864691 := by
  unfold tailWord_1622190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7395766249136269105024003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39444086662060101893461349 7395766249136269105024003)
  ·
    refine ⟨11093649373704403657536005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7395766249136269105024003 11093649373704403657536005)
    ·
      refine ⟨2080059257569575685788001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11093649373704403657536005 2080059257569575685788001)
      ·
        refine ⟨1560044443177181764341001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2080059257569575685788001 1560044443177181764341001)
        ·
          refine ⟨1170033332382886323255751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1560044443177181764341001 1170033332382886323255751)
          ·
            refine ⟨1755049998574329484883627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170033332382886323255751 1755049998574329484883627)
            ·
              refine ⟨2632574997861494227325441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755049998574329484883627 2632574997861494227325441)
              ·
                refine ⟨1974431248396120670494081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632574997861494227325441 1974431248396120670494081)
                ·
                  refine ⟨1480823436297090502870561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974431248396120670494081 1480823436297090502870561)
                  ·
                    refine ⟨1110617577222817877152921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1480823436297090502870561 1110617577222817877152921)
                    ·
                      refine ⟨832963182917113407864691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110617577222817877152921 832963182917113407864691)
                      ·
                        rfl

theorem cell23_1622190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1622190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622190 prefixEnd_1622190 := by exact prefixLift 1622190
  have htrace : WordTrace (prefixWord ++ tailWord_1622190) baseStart_1622190 baseEnd_1622190 := by
    simpa [prefixWord, tailWord_1622190, baseEnd_1622190] using wordTrace_append hprefix tailTrace_1622190
  have hstable : (prefixWord ++ tailWord_1622190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622190).length < 2 ^ (prefixWord ++ tailWord_1622190).sum := by decide
  have hdescent : baseEnd_1622190 < baseStart_1622190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622211 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1622211 : Nat := 118140960795 + 1622211 * 2 ^ 59
def prefixEnd_1622211 : Nat := 4983230072969 + 3 ^ 40 * 1622211 * 2
def baseEnd_1622211 : Nat := 832973966010857825702093

theorem tailTrace_1622211 : CollatzResearch.WordTrace tailWord_1622211 prefixEnd_1622211 832973966010857825702093 := by
  unfold tailWord_1622211
  simp only [CollatzResearch.WordTrace]
  refine ⟨59166895926014073426706487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39444597284009382284470991 59166895926014073426706487)
  ·
    refine ⟨88750343889021110140059731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59166895926014073426706487 88750343889021110140059731)
    ·
      refine ⟨133125515833531665210089597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88750343889021110140059731 133125515833531665210089597)
      ·
        refine ⟨49922068437574374453783599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133125515833531665210089597 49922068437574374453783599)
        ·
          refine ⟨74883102656361561680675399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49922068437574374453783599 74883102656361561680675399)
          ·
            refine ⟨112324653984542342521013099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74883102656361561680675399 112324653984542342521013099)
            ·
              refine ⟨168486980976813513781519649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112324653984542342521013099 168486980976813513781519649)
              ·
                refine ⟨126365235732610135336139737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168486980976813513781519649 126365235732610135336139737)
                ·
                  refine ⟨94773926799457601502104803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126365235732610135336139737 94773926799457601502104803)
                  ·
                    refine ⟨142160890199186402253157205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94773926799457601502104803 142160890199186402253157205)
                    ·
                      refine ⟨832973966010857825702093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 142160890199186402253157205 832973966010857825702093)
                      ·
                        rfl

theorem cell23_1622211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1622211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622211 prefixEnd_1622211 := by exact prefixLift 1622211
  have htrace : WordTrace (prefixWord ++ tailWord_1622211) baseStart_1622211 baseEnd_1622211 := by
    simpa [prefixWord, tailWord_1622211, baseEnd_1622211] using wordTrace_append hprefix tailTrace_1622211
  have hstable : (prefixWord ++ tailWord_1622211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622211).length < 2 ^ (prefixWord ++ tailWord_1622211).sum := by decide
  have hdescent : baseEnd_1622211 < baseStart_1622211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622212 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_1622212 : Nat := 118140960795 + 1622212 * 2 ^ 59
def prefixEnd_1622212 : Nat := 4983230072969 + 3 ^ 40 * 1622212 * 2
def baseEnd_1622212 : Nat := 832974479491512321789589

theorem tailTrace_1622212 : CollatzResearch.WordTrace tailWord_1622212 prefixEnd_1622212 832974479491512321789589 := by
  unfold tailWord_1622212
  simp only [CollatzResearch.WordTrace]
  refine ⟨29583466199505225298746445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39444621599340300398328593 29583466199505225298746445)
  ·
    refine ⟨11093799824814459487029917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29583466199505225298746445 11093799824814459487029917)
    ·
      refine ⟨4160174934305422307636219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11093799824814459487029917 4160174934305422307636219)
      ·
        refine ⟨6240262401458133461454329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160174934305422307636219 6240262401458133461454329)
        ·
          refine ⟨4680196801093600096090747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6240262401458133461454329 4680196801093600096090747)
          ·
            refine ⟨7020295201640400144136121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680196801093600096090747 7020295201640400144136121)
            ·
              refine ⟨5265221401230300108102091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7020295201640400144136121 5265221401230300108102091)
              ·
                refine ⟨7897832101845450162153137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265221401230300108102091 7897832101845450162153137)
                ·
                  refine ⟨5923374076384087621614853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7897832101845450162153137 5923374076384087621614853)
                  ·
                    refine ⟨1110632639322016429052785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923374076384087621614853 1110632639322016429052785)
                    ·
                      refine ⟨832974479491512321789589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110632639322016429052785 832974479491512321789589)
                      ·
                        rfl

theorem cell23_1622212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_1622212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622212 prefixEnd_1622212 := by exact prefixLift 1622212
  have htrace : WordTrace (prefixWord ++ tailWord_1622212) baseStart_1622212 baseEnd_1622212 := by
    simpa [prefixWord, tailWord_1622212, baseEnd_1622212] using wordTrace_append hprefix tailTrace_1622212
  have hstable : (prefixWord ++ tailWord_1622212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622212).length < 2 ^ (prefixWord ++ tailWord_1622212).sum := by decide
  have hdescent : baseEnd_1622212 < baseStart_1622212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622295 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 1, 6]
def baseStart_1622295 : Nat := 118140960795 + 1622295 * 2 ^ 59
def prefixEnd_1622295 : Nat := 4983230072969 + 3 ^ 40 * 1622295 * 2
def baseEnd_1622295 : Nat := 277672366128611832350569

theorem tailTrace_1622295 : CollatzResearch.WordTrace tailWord_1622295 prefixEnd_1622295 277672366128611832350569 := by
  unfold tailWord_1622295
  simp only [CollatzResearch.WordTrace]
  refine ⟨59169959657709755772764339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39446639771806503848509559 59169959657709755772764339)
  ·
    refine ⟨88754939486564633659146509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59169959657709755772764339 88754939486564633659146509)
    ·
      refine ⟨33283102307461737622179941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88754939486564633659146509 33283102307461737622179941)
      ·
        refine ⟨6240581682649075804158739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33283102307461737622179941 6240581682649075804158739)
        ·
          refine ⟨9360872523973613706238109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240581682649075804158739 9360872523973613706238109)
          ·
            refine ⟨3510327196490105139839291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9360872523973613706238109 3510327196490105139839291)
            ·
              refine ⟨5265490794735157709758937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510327196490105139839291 5265490794735157709758937)
              ·
                refine ⟨3949118096051368282319203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265490794735157709758937 3949118096051368282319203)
                ·
                  refine ⟨5923677144077052423478805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949118096051368282319203 5923677144077052423478805)
                  ·
                    refine ⟨277672366128611832350569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5923677144077052423478805 277672366128611832350569)
                    ·
                      rfl

theorem cell23_1622295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_1622295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622295 prefixEnd_1622295 := by exact prefixLift 1622295
  have htrace : WordTrace (prefixWord ++ tailWord_1622295) baseStart_1622295 baseEnd_1622295 := by
    simpa [prefixWord, tailWord_1622295, baseEnd_1622295] using wordTrace_append hprefix tailTrace_1622295
  have hstable : (prefixWord ++ tailWord_1622295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622295).length < 2 ^ (prefixWord ++ tailWord_1622295).sum := by decide
  have hdescent : baseEnd_1622295 < baseStart_1622295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622305 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1622305 : Nat := 118140960795 + 1622305 * 2 ^ 59
def prefixEnd_1622305 : Nat := 4983230072969 + 3 ^ 40 * 1622305 * 2
def baseEnd_1622305 : Nat := 833022233192380457926661

theorem tailTrace_1622305 : CollatzResearch.WordTrace tailWord_1622305 prefixEnd_1622305 833022233192380457926661 := by
  unfold tailWord_1622305
  simp only [CollatzResearch.WordTrace]
  refine ⟨59170324387673527480628369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39446882925115684987085579 59170324387673527480628369)
  ·
    refine ⟨44377743290755145610471277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59170324387673527480628369 44377743290755145610471277)
    ·
      refine ⟨16641653734033179603926729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44377743290755145610471277 16641653734033179603926729)
      ·
        refine ⟨12481240300524884702945047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16641653734033179603926729 12481240300524884702945047)
        ·
          refine ⟨18721860450787327054417571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12481240300524884702945047 18721860450787327054417571)
          ·
            refine ⟨28082790676180990581626357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18721860450787327054417571 28082790676180990581626357)
            ·
              refine ⟨2632761625891967867027471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28082790676180990581626357 2632761625891967867027471)
              ·
                refine ⟨3949142438837951800541207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632761625891967867027471 3949142438837951800541207)
                ·
                  refine ⟨5923713658256927700811811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949142438837951800541207 5923713658256927700811811)
                  ·
                    refine ⟨8885570487385391551217717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923713658256927700811811 8885570487385391551217717)
                    ·
                      refine ⟨833022233192380457926661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8885570487385391551217717 833022233192380457926661)
                      ·
                        rfl

theorem cell23_1622305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1622305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622305 prefixEnd_1622305 := by exact prefixLift 1622305
  have htrace : WordTrace (prefixWord ++ tailWord_1622305) baseStart_1622305 baseEnd_1622305 := by
    simpa [prefixWord, tailWord_1622305, baseEnd_1622305] using wordTrace_append hprefix tailTrace_1622305
  have hstable : (prefixWord ++ tailWord_1622305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622305).length < 2 ^ (prefixWord ++ tailWord_1622305).sum := by decide
  have hdescent : baseEnd_1622305 < baseStart_1622305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622308 : List Nat := [2, 3, 1, 3, 1, 13]
def baseStart_1622308 : Nat := 118140960795 + 1622308 * 2 ^ 59
def prefixEnd_1622308 : Nat := 4983230072969 + 3 ^ 40 * 1622308 * 2
def baseEnd_1622308 : Nat := 3428081372980839284729

theorem tailTrace_1622308 : CollatzResearch.WordTrace tailWord_1622308 prefixEnd_1622308 3428081372980839284729 := by
  unfold tailWord_1622308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29585216903331329496493789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39446955871108439328658385 29585216903331329496493789)
  ·
    refine ⟨11094456338749248561185171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29585216903331329496493789 11094456338749248561185171)
    ·
      refine ⟨16641684508123872841777757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11094456338749248561185171 16641684508123872841777757)
      ·
        refine ⟨6240631690546452315666659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16641684508123872841777757 6240631690546452315666659)
        ·
          refine ⟨9360947535819678473499989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240631690546452315666659 9360947535819678473499989)
          ·
            refine ⟨3428081372980839284729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 9360947535819678473499989 3428081372980839284729)
            ·
              rfl

theorem cell23_1622308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 13].length) (baseStart_1622308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622308 prefixEnd_1622308 := by exact prefixLift 1622308
  have htrace : WordTrace (prefixWord ++ tailWord_1622308) baseStart_1622308 baseEnd_1622308 := by
    simpa [prefixWord, tailWord_1622308, baseEnd_1622308] using wordTrace_append hprefix tailTrace_1622308
  have hstable : (prefixWord ++ tailWord_1622308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622308).length < 2 ^ (prefixWord ++ tailWord_1622308).sum := by decide
  have hdescent : baseEnd_1622308 < baseStart_1622308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622328 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_1622328 : Nat := 118140960795 + 1622328 * 2 ^ 59
def prefixEnd_1622328 : Nat := 4983230072969 + 3 ^ 40 * 1622328 * 2
def baseEnd_1622328 : Nat := 833034043247433867939055

theorem tailTrace_1622328 : CollatzResearch.WordTrace tailWord_1622328 prefixEnd_1622328 833034043247433867939055 := by
  unfold tailWord_1622328
  simp only [CollatzResearch.WordTrace]
  refine ⟨29585581633295101204357819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39447442177726801605810425 29585581633295101204357819)
  ·
    refine ⟨44378372449942651806536729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29585581633295101204357819 44378372449942651806536729)
    ·
      refine ⟨33283779337456988854902547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44378372449942651806536729 33283779337456988854902547)
      ·
        refine ⟨49925669006185483282353821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33283779337456988854902547 49925669006185483282353821)
        ·
          refine ⟨18722125877319556230882683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49925669006185483282353821 18722125877319556230882683)
          ·
            refine ⟨28083188815979334346324025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18722125877319556230882683 28083188815979334346324025)
            ·
              refine ⟨21062391611984500759743019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28083188815979334346324025 21062391611984500759743019)
              ·
                refine ⟨31593587417976751139614529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21062391611984500759743019 31593587417976751139614529)
                ·
                  refine ⟨23695190563482563354710897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31593587417976751139614529 23695190563482563354710897)
                  ·
                    refine ⟨17771392922611922516033173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23695190563482563354710897 17771392922611922516033173)
                    ·
                      refine ⟨833034043247433867939055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17771392922611922516033173 833034043247433867939055)
                      ·
                        rfl

theorem cell23_1622328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_1622328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622328 prefixEnd_1622328 := by exact prefixLift 1622328
  have htrace : WordTrace (prefixWord ++ tailWord_1622328) baseStart_1622328 baseEnd_1622328 := by
    simpa [prefixWord, tailWord_1622328, baseEnd_1622328] using wordTrace_append hprefix tailTrace_1622328
  have hstable : (prefixWord ++ tailWord_1622328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622328).length < 2 ^ (prefixWord ++ tailWord_1622328).sum := by decide
  have hdescent : baseEnd_1622328 < baseStart_1622328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622356 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_1622356 : Nat := 118140960795 + 1622356 * 2 ^ 59
def prefixEnd_1622356 : Nat := 4983230072969 + 3 ^ 40 * 1622356 * 2
def baseEnd_1622356 : Nat := 833048420705759758388927

theorem tailTrace_1622356 : CollatzResearch.WordTrace tailWord_1622356 prefixEnd_1622356 833048420705759758388927 := by
  unfold tailWord_1622356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29586092255244381595367461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39448123006992508793823281 29586092255244381595367461)
  ·
    refine ⟨5547392297858321549131399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29586092255244381595367461 5547392297858321549131399)
    ·
      refine ⟨8321088446787482323697099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547392297858321549131399 8321088446787482323697099)
      ·
        refine ⟨12481632670181223485545649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8321088446787482323697099 12481632670181223485545649)
        ·
          refine ⟨9361224502635917614159237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12481632670181223485545649 9361224502635917614159237)
          ·
            refine ⟨1755229594244234552654857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9361224502635917614159237 1755229594244234552654857)
            ·
              refine ⟨1316422195683175914491143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755229594244234552654857 1316422195683175914491143)
              ·
                refine ⟨1974633293524763871736715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316422195683175914491143 1974633293524763871736715)
                ·
                  refine ⟨2961949940287145807605073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974633293524763871736715 2961949940287145807605073)
                  ·
                    refine ⟨2221462455215359355703805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2961949940287145807605073 2221462455215359355703805)
                    ·
                      refine ⟨833048420705759758388927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2221462455215359355703805 833048420705759758388927)
                      ·
                        rfl

theorem cell23_1622356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_1622356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622356 prefixEnd_1622356 := by exact prefixLift 1622356
  have htrace : WordTrace (prefixWord ++ tailWord_1622356) baseStart_1622356 baseEnd_1622356 := by
    simpa [prefixWord, tailWord_1622356, baseEnd_1622356] using wordTrace_append hprefix tailTrace_1622356
  have hstable : (prefixWord ++ tailWord_1622356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622356).length < 2 ^ (prefixWord ++ tailWord_1622356).sum := by decide
  have hdescent : baseEnd_1622356 < baseStart_1622356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622386 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_1622386 : Nat := 118140960795 + 1622386 * 2 ^ 59
def prefixEnd_1622386 : Nat := 4983230072969 + 3 ^ 40 * 1622386 * 2
def baseEnd_1622386 : Nat := 833063825125394641013789

theorem tailTrace_1622386 : CollatzResearch.WordTrace tailWord_1622386 prefixEnd_1622386 833063825125394641013789 := by
  unfold tailWord_1622386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14793319675095019578581753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39448852466920052209551341 14793319675095019578581753)
  ·
    refine ⟨11094989756321264683936315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14793319675095019578581753 11094989756321264683936315)
    ·
      refine ⟨16642484634481897025904473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11094989756321264683936315 16642484634481897025904473)
      ·
        refine ⟨12481863475861422769428355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16642484634481897025904473 12481863475861422769428355)
        ·
          refine ⟨18722795213792134154142533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12481863475861422769428355 18722795213792134154142533)
          ·
            refine ⟨3510524102586025153901725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18722795213792134154142533 3510524102586025153901725)
            ·
              refine ⟨1316446538469759432713147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510524102586025153901725 1316446538469759432713147)
              ·
                refine ⟨1974669807704639149069721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316446538469759432713147 1974669807704639149069721)
                ·
                  refine ⟨1481002355778479361802291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974669807704639149069721 1481002355778479361802291)
                  ·
                    refine ⟨2221503533667719042703437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1481002355778479361802291 2221503533667719042703437)
                    ·
                      refine ⟨833063825125394641013789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2221503533667719042703437 833063825125394641013789)
                      ·
                        rfl

theorem cell23_1622386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_1622386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622386 prefixEnd_1622386 := by exact prefixLift 1622386
  have htrace : WordTrace (prefixWord ++ tailWord_1622386) baseStart_1622386 baseEnd_1622386 := by
    simpa [prefixWord, tailWord_1622386, baseEnd_1622386] using wordTrace_append hprefix tailTrace_1622386
  have hstable : (prefixWord ++ tailWord_1622386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622386).length < 2 ^ (prefixWord ++ tailWord_1622386).sum := by decide
  have hdescent : baseEnd_1622386 < baseStart_1622386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622409 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 4, 2, 2]
def baseStart_1622409 : Nat := 118140960795 + 1622409 * 2 ^ 59
def prefixEnd_1622409 : Nat := 4983230072969 + 3 ^ 40 * 1622409 * 2
def baseEnd_1622409 : Nat := 833075635180448051026183

theorem tailTrace_1622409 : CollatzResearch.WordTrace tailWord_1622409 prefixEnd_1622409 833075635180448051026183 := by
  unfold tailWord_1622409
  simp only [CollatzResearch.WordTrace]
  refine ⟨59174117579296753242414281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39449411719531168828276187 59174117579296753242414281)
  ·
    refine ⟨44380588184472564931810711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59174117579296753242414281 44380588184472564931810711)
    ·
      refine ⟨66570882276708847397716067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44380588184472564931810711 66570882276708847397716067)
      ·
        refine ⟨99856323415063271096574101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66570882276708847397716067 99856323415063271096574101)
        ·
          refine ⟨4680765160081090832651911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99856323415063271096574101 4680765160081090832651911)
          ·
            refine ⟨7021147740121636248977867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680765160081090832651911 7021147740121636248977867)
            ·
              refine ⟨10531721610182454373466801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021147740121636248977867 10531721610182454373466801)
              ·
                refine ⟨7898791207636840780100101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10531721610182454373466801 7898791207636840780100101)
                ·
                  refine ⟨1481023351431907646268769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7898791207636840780100101 1481023351431907646268769)
                  ·
                    refine ⟨1110767513573930734701577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1481023351431907646268769 1110767513573930734701577)
                    ·
                      refine ⟨833075635180448051026183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1110767513573930734701577 833075635180448051026183)
                      ·
                        rfl

theorem cell23_1622409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 2, 2].length) (baseStart_1622409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622409 prefixEnd_1622409 := by exact prefixLift 1622409
  have htrace : WordTrace (prefixWord ++ tailWord_1622409) baseStart_1622409 baseEnd_1622409 := by
    simpa [prefixWord, tailWord_1622409, baseEnd_1622409] using wordTrace_append hprefix tailTrace_1622409
  have hstable : (prefixWord ++ tailWord_1622409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622409).length < 2 ^ (prefixWord ++ tailWord_1622409).sum := by decide
  have hdescent : baseEnd_1622409 < baseStart_1622409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622432 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 7]
def baseStart_1622432 : Nat := 118140960795 + 1622432 * 2 ^ 59
def prefixEnd_1622432 : Nat := 4983230072969 + 3 ^ 40 * 1622432 * 2
def baseEnd_1622432 : Nat := 92565271692833495670953

theorem tailTrace_1622432 : CollatzResearch.WordTrace tailWord_1622432 prefixEnd_1622432 92565271692833495670953 := by
  unfold tailWord_1622432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29587478229106714085250775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39449970972142285447001033 29587478229106714085250775)
  ·
    refine ⟨44381217343660071127876163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29587478229106714085250775 44381217343660071127876163)
    ·
      refine ⟨66571826015490106691814245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44381217343660071127876163 66571826015490106691814245)
      ·
        refine ⟨12482217377904395004715171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66571826015490106691814245 12482217377904395004715171)
        ·
          refine ⟨18723326066856592507072757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12482217377904395004715171 18723326066856592507072757)
          ·
            refine ⟨1755311818767805547538071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18723326066856592507072757 1755311818767805547538071)
            ·
              refine ⟨2632967728151708321307107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755311818767805547538071 2632967728151708321307107)
              ·
                refine ⟨3949451592227562481960661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632967728151708321307107 3949451592227562481960661)
                ·
                  refine ⟨92565271692833495670953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3949451592227562481960661 92565271692833495670953)
                  ·
                    rfl

theorem cell23_1622432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 7].length) (baseStart_1622432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622432 prefixEnd_1622432 := by exact prefixLift 1622432
  have htrace : WordTrace (prefixWord ++ tailWord_1622432) baseStart_1622432 baseEnd_1622432 := by
    simpa [prefixWord, tailWord_1622432, baseEnd_1622432] using wordTrace_append hprefix tailTrace_1622432
  have hstable : (prefixWord ++ tailWord_1622432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622432).length < 2 ^ (prefixWord ++ tailWord_1622432).sum := by decide
  have hdescent : baseEnd_1622432 < baseStart_1622432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622462 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1622462 : Nat := 118140960795 + 1622462 * 2 ^ 59
def prefixEnd_1622462 : Nat := 4983230072969 + 3 ^ 40 * 1622462 * 2
def baseEnd_1622462 : Nat := 277700949885045447887813

theorem tailTrace_1622462 : CollatzResearch.WordTrace tailWord_1622462 prefixEnd_1622462 277700949885045447887813 := by
  unfold tailWord_1622462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397006331013092911761705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39450700432069828862729093 7397006331013092911761705)
  ·
    refine ⟨5547754748259819683821279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7397006331013092911761705 5547754748259819683821279)
    ·
      refine ⟨8321632122389729525731919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547754748259819683821279 8321632122389729525731919)
      ·
        refine ⟨12482448183584594288597879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8321632122389729525731919 12482448183584594288597879)
        ·
          refine ⟨18723672275376891432896819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12482448183584594288597879 18723672275376891432896819)
          ·
            refine ⟨28085508413065337149345229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18723672275376891432896819 28085508413065337149345229)
            ·
              refine ⟨10532065654899501431004461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28085508413065337149345229 10532065654899501431004461)
              ·
                refine ⟨3949524620587313036626673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10532065654899501431004461 3949524620587313036626673)
                ·
                  refine ⟨2962143465440484777470005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3949524620587313036626673 2962143465440484777470005)
                  ·
                    refine ⟨277700949885045447887813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2962143465440484777470005 277700949885045447887813)
                    ·
                      rfl

theorem cell23_1622462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1622462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622462 prefixEnd_1622462 := by exact prefixLift 1622462
  have htrace : WordTrace (prefixWord ++ tailWord_1622462) baseStart_1622462 baseEnd_1622462 := by
    simpa [prefixWord, tailWord_1622462, baseEnd_1622462] using wordTrace_append hprefix tailTrace_1622462
  have hstable : (prefixWord ++ tailWord_1622462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622462).length < 2 ^ (prefixWord ++ tailWord_1622462).sum := by decide
  have hdescent : baseEnd_1622462 < baseStart_1622462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622509 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_1622509 : Nat := 118140960795 + 1622509 * 2 ^ 59
def prefixEnd_1622509 : Nat := 4983230072969 + 3 ^ 40 * 1622509 * 2
def baseEnd_1622509 : Nat := 277708994415299219925241

theorem tailTrace_1622509 : CollatzResearch.WordTrace tailWord_1622509 prefixEnd_1622509 277708994415299219925241 := by
  unfold tailWord_1622509
  simp only [CollatzResearch.WordTrace]
  refine ⟨59177764878934470321054581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39451843252622980214036387 59177764878934470321054581)
  ·
    refine ⟨5547915457400106592598867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59177764878934470321054581 5547915457400106592598867)
    ·
      refine ⟨8321873186100159888898301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547915457400106592598867 8321873186100159888898301)
      ·
        refine ⟨3120702444787559958336863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8321873186100159888898301 3120702444787559958336863)
        ·
          refine ⟨4681053667181339937505295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120702444787559958336863 4681053667181339937505295)
          ·
            refine ⟨7021580500772009906257943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681053667181339937505295 7021580500772009906257943)
            ·
              refine ⟨10532370751158014859386915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021580500772009906257943 10532370751158014859386915)
              ·
                refine ⟨15798556126737022289080373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10532370751158014859386915 15798556126737022289080373)
                ·
                  refine ⟨1481114636881595839601285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15798556126737022289080373 1481114636881595839601285)
                  ·
                    refine ⟨277708994415299219925241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1481114636881595839601285 277708994415299219925241)
                    ·
                      rfl

theorem cell23_1622509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_1622509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622509 prefixEnd_1622509 := by exact prefixLift 1622509
  have htrace : WordTrace (prefixWord ++ tailWord_1622509) baseStart_1622509 baseEnd_1622509 := by
    simpa [prefixWord, tailWord_1622509, baseEnd_1622509] using wordTrace_append hprefix tailTrace_1622509
  have hstable : (prefixWord ++ tailWord_1622509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622509).length < 2 ^ (prefixWord ++ tailWord_1622509).sum := by decide
  have hdescent : baseEnd_1622509 < baseStart_1622509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622539 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 6]
def baseStart_1622539 : Nat := 118140960795 + 1622539 * 2 ^ 59
def prefixEnd_1622539 : Nat := 4983230072969 + 3 ^ 40 * 1622539 * 2
def baseEnd_1622539 : Nat := 92571376407281393600065

theorem tailTrace_1622539 : CollatzResearch.WordTrace tailWord_1622539 prefixEnd_1622539 92571376407281393600065 := by
  unfold tailWord_1622539
  simp only [CollatzResearch.WordTrace]
  refine ⟨59178859068825785444646671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39452572712550523629764447 59178859068825785444646671)
  ·
    refine ⟨88768288603238678166970007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59178859068825785444646671 88768288603238678166970007)
    ·
      refine ⟨133152432904858017250455011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88768288603238678166970007 133152432904858017250455011)
      ·
        refine ⟨199728649357287025875682517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133152432904858017250455011 199728649357287025875682517)
        ·
          refine ⟨4681140219311414668961309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 199728649357287025875682517 4681140219311414668961309)
          ·
            refine ⟨1755427582241780500860491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4681140219311414668961309 1755427582241780500860491)
            ·
              refine ⟨2633141373362670751290737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755427582241780500860491 2633141373362670751290737)
              ·
                refine ⟨1974856030022003063468053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633141373362670751290737 1974856030022003063468053)
                ·
                  refine ⟨92571376407281393600065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1974856030022003063468053 92571376407281393600065)
                  ·
                    rfl

theorem cell23_1622539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 6].length) (baseStart_1622539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622539 prefixEnd_1622539 := by exact prefixLift 1622539
  have htrace : WordTrace (prefixWord ++ tailWord_1622539) baseStart_1622539 baseEnd_1622539 := by
    simpa [prefixWord, tailWord_1622539, baseEnd_1622539] using wordTrace_append hprefix tailTrace_1622539
  have hstable : (prefixWord ++ tailWord_1622539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622539).length < 2 ^ (prefixWord ++ tailWord_1622539).sum := by decide
  have hdescent : baseEnd_1622539 < baseStart_1622539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622542 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1622542 : Nat := 118140960795 + 1622542 * 2 ^ 59
def prefixEnd_1622542 : Nat := 4983230072969 + 3 ^ 40 * 1622542 * 2
def baseEnd_1622542 : Nat := 833143928107496030663071

theorem tailTrace_1622542 : CollatzResearch.WordTrace tailWord_1622542 prefixEnd_1622542 833143928107496030663071 := by
  unfold tailWord_1622542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397371060976864619625735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39452645658543277971337253 7397371060976864619625735)
  ·
    refine ⟨11096056591465296929438603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7397371060976864619625735 11096056591465296929438603)
    ·
      refine ⟨16644084887197945394157905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11096056591465296929438603 16644084887197945394157905)
      ·
        refine ⟨12483063665398459045618429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16644084887197945394157905 12483063665398459045618429)
        ·
          refine ⟨4681148874524422142106911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12483063665398459045618429 4681148874524422142106911)
          ·
            refine ⟨7021723311786633213160367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681148874524422142106911 7021723311786633213160367)
            ·
              refine ⟨10532584967679949819740551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021723311786633213160367 10532584967679949819740551)
              ·
                refine ⟨15798877451519924729610827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10532584967679949819740551 15798877451519924729610827)
                ·
                  refine ⟨23698316177279887094416241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15798877451519924729610827 23698316177279887094416241)
                  ·
                    refine ⟨17773737132959915320812181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23698316177279887094416241 17773737132959915320812181)
                    ·
                      refine ⟨833143928107496030663071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17773737132959915320812181 833143928107496030663071)
                      ·
                        rfl

theorem cell23_1622542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1622542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622542 prefixEnd_1622542 := by exact prefixLift 1622542
  have htrace : WordTrace (prefixWord ++ tailWord_1622542) baseStart_1622542 baseEnd_1622542 := by
    simpa [prefixWord, tailWord_1622542, baseEnd_1622542] using wordTrace_append hprefix tailTrace_1622542
  have hstable : (prefixWord ++ tailWord_1622542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622542).length < 2 ^ (prefixWord ++ tailWord_1622542).sum := by decide
  have hdescent : baseEnd_1622542 < baseStart_1622542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622545 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_1622545 : Nat := 118140960795 + 1622545 * 2 ^ 59
def prefixEnd_1622545 : Nat := 4983230072969 + 3 ^ 40 * 1622545 * 2
def baseEnd_1622545 : Nat := 833145468549459518925557

theorem tailTrace_1622545 : CollatzResearch.WordTrace tailWord_1622545 prefixEnd_1622545 833145468549459518925557 := by
  unfold tailWord_1622545
  simp only [CollatzResearch.WordTrace]
  refine ⟨59179077906804048469365089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39452718604536032312910059 59179077906804048469365089)
  ·
    refine ⟨44384308430103036352023817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59179077906804048469365089 44384308430103036352023817)
    ·
      refine ⟨33288231322577277264017863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44384308430103036352023817 33288231322577277264017863)
      ·
        refine ⟨49932346983865915896026795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33288231322577277264017863 49932346983865915896026795)
        ·
          refine ⟨74898520475798873844040193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49932346983865915896026795 74898520475798873844040193)
          ·
            refine ⟨56173890356849155383030145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74898520475798873844040193 56173890356849155383030145)
            ·
              refine ⟨42130417767636866537272609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56173890356849155383030145 42130417767636866537272609)
              ·
                refine ⟨31597813325727649902954457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42130417767636866537272609 31597813325727649902954457)
                ·
                  refine ⟨23698359994295737427215843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31597813325727649902954457 23698359994295737427215843)
                  ·
                    refine ⟨35547539991443606140823765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23698359994295737427215843 35547539991443606140823765)
                    ·
                      refine ⟨833145468549459518925557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35547539991443606140823765 833145468549459518925557)
                      ·
                        rfl

theorem cell23_1622545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_1622545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622545 prefixEnd_1622545 := by exact prefixLift 1622545
  have htrace : WordTrace (prefixWord ++ tailWord_1622545) baseStart_1622545 baseEnd_1622545 := by
    simpa [prefixWord, tailWord_1622545, baseEnd_1622545] using wordTrace_append hprefix tailTrace_1622545
  have hstable : (prefixWord ++ tailWord_1622545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622545).length < 2 ^ (prefixWord ++ tailWord_1622545).sum := by decide
  have hdescent : baseEnd_1622545 < baseStart_1622545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622572 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_1622572 : Nat := 118140960795 + 1622572 * 2 ^ 59
def prefixEnd_1622572 : Nat := 4983230072969 + 3 ^ 40 * 1622572 * 2
def baseEnd_1622572 : Nat := 833159332527130913287933

theorem tailTrace_1622572 : CollatzResearch.WordTrace tailWord_1622572 prefixEnd_1622572 833159332527130913287933 := by
  unfold tailWord_1622572
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590031338853116040298985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39453375118470821387065313 29590031338853116040298985)
  ·
    refine ⟨22192523504139837030224239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29590031338853116040298985 22192523504139837030224239)
    ·
      refine ⟨33288785256209755545336359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22192523504139837030224239 33288785256209755545336359)
      ·
        refine ⟨49933177884314633318004539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33288785256209755545336359 49933177884314633318004539)
        ·
          refine ⟨74899766826471949977006809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49933177884314633318004539 74899766826471949977006809)
          ·
            refine ⟨56174825119853962482755107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74899766826471949977006809 56174825119853962482755107)
            ·
              refine ⟨84262237679780943724132661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56174825119853962482755107 84262237679780943724132661)
              ·
                refine ⟨7899584782479463474137437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84262237679780943724132661 7899584782479463474137437)
                ·
                  refine ⟨2962344293429798802801539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7899584782479463474137437 2962344293429798802801539)
                  ·
                    refine ⟨4443516440144698204202309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2962344293429798802801539 4443516440144698204202309)
                    ·
                      refine ⟨833159332527130913287933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4443516440144698204202309 833159332527130913287933)
                      ·
                        rfl

theorem cell23_1622572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_1622572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622572 prefixEnd_1622572 := by exact prefixLift 1622572
  have htrace : WordTrace (prefixWord ++ tailWord_1622572) baseStart_1622572 baseEnd_1622572 := by
    simpa [prefixWord, tailWord_1622572, baseEnd_1622572] using wordTrace_append hprefix tailTrace_1622572
  have hstable : (prefixWord ++ tailWord_1622572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622572).length < 2 ^ (prefixWord ++ tailWord_1622572).sum := by decide
  have hdescent : baseEnd_1622572 < baseStart_1622572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622592 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_1622592 : Nat := 118140960795 + 1622592 * 2 ^ 59
def prefixEnd_1622592 : Nat := 4983230072969 + 3 ^ 40 * 1622592 * 2
def baseEnd_1622592 : Nat := 833169602140220835037841

theorem tailTrace_1622592 : CollatzResearch.WordTrace tailWord_1622592 prefixEnd_1622592 833169602140220835037841 := by
  unfold tailWord_1622592
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590396068816887748163015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39453861425089183664217353 29590396068816887748163015)
  ·
    refine ⟨44385594103225331622244523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29590396068816887748163015 44385594103225331622244523)
    ·
      refine ⟨66578391154837997433366785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44385594103225331622244523 66578391154837997433366785)
      ·
        refine ⟨49933793366128498075025089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66578391154837997433366785 49933793366128498075025089)
        ·
          refine ⟨37450345024596373556268817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49933793366128498075025089 37450345024596373556268817)
          ·
            refine ⟨28087758768447280167201613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37450345024596373556268817 28087758768447280167201613)
            ·
              refine ⟨10532909538167730062700605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28087758768447280167201613 10532909538167730062700605)
              ·
                refine ⟨3949841076812898773512727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10532909538167730062700605 3949841076812898773512727)
                ·
                  refine ⟨5924761615219348160269091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949841076812898773512727 5924761615219348160269091)
                  ·
                    refine ⟨8887142422829022240403637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5924761615219348160269091 8887142422829022240403637)
                    ·
                      refine ⟨833169602140220835037841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8887142422829022240403637 833169602140220835037841)
                      ·
                        rfl

theorem cell23_1622592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_1622592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622592 prefixEnd_1622592 := by exact prefixLift 1622592
  have htrace : WordTrace (prefixWord ++ tailWord_1622592) baseStart_1622592 baseEnd_1622592 := by
    simpa [prefixWord, tailWord_1622592, baseEnd_1622592] using wordTrace_append hprefix tailTrace_1622592
  have hstable : (prefixWord ++ tailWord_1622592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622592).length < 2 ^ (prefixWord ++ tailWord_1622592).sum := by decide
  have hdescent : baseEnd_1622592 < baseStart_1622592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622599 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 4, 4]
def baseStart_1622599 : Nat := 118140960795 + 1622599 * 2 ^ 59
def prefixEnd_1622599 : Nat := 4983230072969 + 3 ^ 40 * 1622599 * 2
def baseEnd_1622599 : Nat := 277724398834934102550103

theorem tailTrace_1622599 : CollatzResearch.WordTrace tailWord_1622599 prefixEnd_1622599 277724398834934102550103 := by
  unfold tailWord_1622599
  simp only [CollatzResearch.WordTrace]
  refine ⟨59181047448608415691830851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39454031632405610461220567 59181047448608415691830851)
  ·
    refine ⟨88771571172912623537746277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59181047448608415691830851 88771571172912623537746277)
    ·
      refine ⟨16644669594921116913327427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88771571172912623537746277 16644669594921116913327427)
      ·
        refine ⟨24967004392381675369991141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16644669594921116913327427 24967004392381675369991141)
        ·
          refine ⟨4681313323571564131873339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24967004392381675369991141 4681313323571564131873339)
          ·
            refine ⟨7021969985357346197810009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681313323571564131873339 7021969985357346197810009)
            ·
              refine ⟨5266477489018009648357507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7021969985357346197810009 5266477489018009648357507)
              ·
                refine ⟨7899716233527014472536261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266477489018009648357507 7899716233527014472536261)
                ·
                  refine ⟨1481196793786315213600549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7899716233527014472536261 1481196793786315213600549)
                  ·
                    refine ⟨277724398834934102550103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1481196793786315213600549 277724398834934102550103)
                    ·
                      rfl

theorem cell23_1622599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_1622599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622599 prefixEnd_1622599 := by exact prefixLift 1622599
  have htrace : WordTrace (prefixWord ++ tailWord_1622599) baseStart_1622599 baseEnd_1622599 := by
    simpa [prefixWord, tailWord_1622599, baseEnd_1622599] using wordTrace_append hprefix tailTrace_1622599
  have hstable : (prefixWord ++ tailWord_1622599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622599).length < 2 ^ (prefixWord ++ tailWord_1622599).sum := by decide
  have hdescent : baseEnd_1622599 < baseStart_1622599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622602 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1622602 : Nat := 118140960795 + 1622602 * 2 ^ 59
def prefixEnd_1622602 : Nat := 4983230072969 + 3 ^ 40 * 1622602 * 2
def baseEnd_1622602 : Nat := 833174736946765795912795

theorem tailTrace_1622602 : CollatzResearch.WordTrace tailWord_1622602 prefixEnd_1622602 833174736946765795912795 := by
  unfold tailWord_1622602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14795289216899386801047515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39454104578398364802793373 14795289216899386801047515)
  ·
    refine ⟨22192933825349080201571273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14795289216899386801047515 22192933825349080201571273)
    ·
      refine ⟨16644700369011810151178455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22192933825349080201571273 16644700369011810151178455)
      ·
        refine ⟨24967050553517715226767683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16644700369011810151178455 24967050553517715226767683)
        ·
          refine ⟨37450575830276572840151525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24967050553517715226767683 37450575830276572840151525)
          ·
            refine ⟨7021982968176857407528411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37450575830276572840151525 7021982968176857407528411)
            ·
              refine ⟨10532974452265286111292617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021982968176857407528411 10532974452265286111292617)
              ·
                refine ⟨7899730839198964583469463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10532974452265286111292617 7899730839198964583469463)
                ·
                  refine ⟨11849596258798446875204195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899730839198964583469463 11849596258798446875204195)
                  ·
                    refine ⟨17774394388197670312806293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11849596258798446875204195 17774394388197670312806293)
                    ·
                      refine ⟨833174736946765795912795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17774394388197670312806293 833174736946765795912795)
                      ·
                        rfl

theorem cell23_1622602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1622602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622602 prefixEnd_1622602 := by exact prefixLift 1622602
  have htrace : WordTrace (prefixWord ++ tailWord_1622602) baseStart_1622602 baseEnd_1622602 := by
    simpa [prefixWord, tailWord_1622602, baseEnd_1622602] using wordTrace_append hprefix tailTrace_1622602
  have hstable : (prefixWord ++ tailWord_1622602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622602).length < 2 ^ (prefixWord ++ tailWord_1622602).sum := by decide
  have hdescent : baseEnd_1622602 < baseStart_1622602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622612 : List Nat := [2, 4, 1, 1, 1, 3, 1, 10]
def baseStart_1622612 : Nat := 118140960795 + 1622612 * 2 ^ 59
def prefixEnd_1622612 : Nat := 4983230072969 + 3 ^ 40 * 1622612 * 2
def baseEnd_1622612 : Nat := 30858513768641139140287

theorem tailTrace_1622612 : CollatzResearch.WordTrace tailWord_1622612 prefixEnd_1622612 30858513768641139140287 := by
  unfold tailWord_1622612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590760798780659456027045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39454347731707545941369393 29590760798780659456027045)
  ·
    refine ⟨5548267649771373648005071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29590760798780659456027045 5548267649771373648005071)
    ·
      refine ⟨8322401474657060472007607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5548267649771373648005071 8322401474657060472007607)
      ·
        refine ⟨12483602211985590708011411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8322401474657060472007607 12483602211985590708011411)
        ·
          refine ⟨18725403317978386062017117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12483602211985590708011411 18725403317978386062017117)
          ·
            refine ⟨7022026244241894773256419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18725403317978386062017117 7022026244241894773256419)
            ·
              refine ⟨10533039366362842159884629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7022026244241894773256419 10533039366362842159884629)
              ·
                refine ⟨30858513768641139140287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10533039366362842159884629 30858513768641139140287)
                ·
                  rfl

theorem cell23_1622612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 10].length) (baseStart_1622612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622612 prefixEnd_1622612 := by exact prefixLift 1622612
  have htrace : WordTrace (prefixWord ++ tailWord_1622612) baseStart_1622612 baseEnd_1622612 := by
    simpa [prefixWord, tailWord_1622612, baseEnd_1622612] using wordTrace_append hprefix tailTrace_1622612
  have hstable : (prefixWord ++ tailWord_1622612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622612).length < 2 ^ (prefixWord ++ tailWord_1622612).sum := by decide
  have hdescent : baseEnd_1622612 < baseStart_1622612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622616 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 2, 4]
def baseStart_1622616 : Nat := 118140960795 + 1622616 * 2 ^ 59
def prefixEnd_1622616 : Nat := 4983230072969 + 3 ^ 40 * 1622616 * 2
def baseEnd_1622616 : Nat := 277727308558642913712577

theorem tailTrace_1622616 : CollatzResearch.WordTrace tailWord_1622616 prefixEnd_1622616 277727308558642913712577 := by
  unfold tailWord_1622616
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590833744773413797599851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39454444993031218396799801 29590833744773413797599851)
  ·
    refine ⟨44386250617160120696399777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29590833744773413797599851 44386250617160120696399777)
    ·
      refine ⟨33289687962870090522299833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44386250617160120696399777 33289687962870090522299833)
      ·
        refine ⟨24967265972152567891724875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33289687962870090522299833 24967265972152567891724875)
        ·
          refine ⟨37450898958228851837587313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24967265972152567891724875 37450898958228851837587313)
          ·
            refine ⟨28088174218671638878190485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37450898958228851837587313 28088174218671638878190485)
            ·
              refine ⟨1316633166500233072415179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28088174218671638878190485 1316633166500233072415179)
              ·
                refine ⟨1974949749750349608622769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316633166500233072415179 1974949749750349608622769)
                ·
                  refine ⟨1481212312312762206467077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974949749750349608622769 1481212312312762206467077)
                  ·
                    refine ⟨277727308558642913712577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1481212312312762206467077 277727308558642913712577)
                    ·
                      rfl

theorem cell23_1622616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_1622616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622616 prefixEnd_1622616 := by exact prefixLift 1622616
  have htrace : WordTrace (prefixWord ++ tailWord_1622616) baseStart_1622616 baseEnd_1622616 := by
    simpa [prefixWord, tailWord_1622616, baseEnd_1622616] using wordTrace_append hprefix tailTrace_1622616
  have hstable : (prefixWord ++ tailWord_1622616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622616).length < 2 ^ (prefixWord ++ tailWord_1622616).sum := by decide
  have hdescent : baseEnd_1622616 < baseStart_1622616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622639 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 3]
def baseStart_1622639 : Nat := 118140960795 + 1622639 * 2 ^ 59
def prefixEnd_1622639 : Nat := 4983230072969 + 3 ^ 40 * 1622639 * 2
def baseEnd_1622639 : Nat := 833193735730982151150125

theorem tailTrace_1622639 : CollatzResearch.WordTrace tailWord_1622639 prefixEnd_1622639 833193735730982151150125 := by
  unfold tailWord_1622639
  simp only [CollatzResearch.WordTrace]
  refine ⟨59182506368463502523286971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39455004245642335015524647 59182506368463502523286971)
  ·
    refine ⟨88773759552695253784930457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59182506368463502523286971 88773759552695253784930457)
    ·
      refine ⟨66580319664521440338697843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88773759552695253784930457 66580319664521440338697843)
      ·
        refine ⟨99870479496782160508046765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66580319664521440338697843 99870479496782160508046765)
        ·
          refine ⟨37451429811293310190517537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99870479496782160508046765 37451429811293310190517537)
          ·
            refine ⟨28088572358469982642888153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37451429811293310190517537 28088572358469982642888153)
            ·
              refine ⟨21066429268852486982166115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28088572358469982642888153 21066429268852486982166115)
              ·
                refine ⟨31599643903278730473249173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21066429268852486982166115 31599643903278730473249173)
                ·
                  refine ⟨1481233307966190490933555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31599643903278730473249173 1481233307966190490933555)
                  ·
                    refine ⟨2221849961949285736400333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1481233307966190490933555 2221849961949285736400333)
                    ·
                      refine ⟨833193735730982151150125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2221849961949285736400333 833193735730982151150125)
                      ·
                        rfl

theorem cell23_1622639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_1622639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622639 prefixEnd_1622639 := by exact prefixLift 1622639
  have htrace : WordTrace (prefixWord ++ tailWord_1622639) baseStart_1622639 baseEnd_1622639 := by
    simpa [prefixWord, tailWord_1622639, baseEnd_1622639] using wordTrace_append hprefix tailTrace_1622639
  have hstable : (prefixWord ++ tailWord_1622639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622639).length < 2 ^ (prefixWord ++ tailWord_1622639).sum := by decide
  have hdescent : baseEnd_1622639 < baseStart_1622639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622652 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_1622652 : Nat := 118140960795 + 1622652 * 2 ^ 59
def prefixEnd_1622652 : Nat := 4983230072969 + 3 ^ 40 * 1622652 * 2
def baseEnd_1622652 : Nat := 833200410979490600287565

theorem tailTrace_1622652 : CollatzResearch.WordTrace tailWord_1622652 prefixEnd_1622652 833200410979490600287565 := by
  unfold tailWord_1622652
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591490258708202871755105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39455320344944270495673473 29591490258708202871755105)
  ·
    refine ⟨22193617694031152153816329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29591490258708202871755105 22193617694031152153816329)
    ·
      refine ⟨16645213270523364115362247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22193617694031152153816329 16645213270523364115362247)
      ·
        refine ⟨24967819905785046173043371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16645213270523364115362247 24967819905785046173043371)
        ·
          refine ⟨37451729858677569259565057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24967819905785046173043371 37451729858677569259565057)
          ·
            refine ⟨28088797394008176944673793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37451729858677569259565057 28088797394008176944673793)
            ·
              refine ⟨21066598045506132708505345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28088797394008176944673793 21066598045506132708505345)
              ·
                refine ⟨15799948534129599531379009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21066598045506132708505345 15799948534129599531379009)
                ·
                  refine ⟨11849961400597199648534257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15799948534129599531379009 11849961400597199648534257)
                  ·
                    refine ⟨8887471050447899736400693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11849961400597199648534257 8887471050447899736400693)
                    ·
                      refine ⟨833200410979490600287565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8887471050447899736400693 833200410979490600287565)
                      ·
                        rfl

theorem cell23_1622652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_1622652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622652 prefixEnd_1622652 := by exact prefixLift 1622652
  have htrace : WordTrace (prefixWord ++ tailWord_1622652) baseStart_1622652 baseEnd_1622652 := by
    simpa [prefixWord, tailWord_1622652, baseEnd_1622652] using wordTrace_append hprefix tailTrace_1622652
  have hstable : (prefixWord ++ tailWord_1622652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622652).length < 2 ^ (prefixWord ++ tailWord_1622652).sum := by decide
  have hdescent : baseEnd_1622652 < baseStart_1622652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622656 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 2, 1, 3]
def baseStart_1622656 : Nat := 118140960795 + 1622656 * 2 ^ 59
def prefixEnd_1622656 : Nat := 4983230072969 + 3 ^ 40 * 1622656 * 2
def baseEnd_1622656 : Nat := 833202464902108584637547

theorem tailTrace_1622656 : CollatzResearch.WordTrace tailWord_1622656 prefixEnd_1622656 833202464902108584637547 := by
  unfold tailWord_1622656
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591563204700957213327911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39455417606267942951103881 29591563204700957213327911)
  ·
    refine ⟨44387344807051435819991867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29591563204700957213327911 44387344807051435819991867)
    ·
      refine ⟨66581017210577153729987801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44387344807051435819991867 66581017210577153729987801)
      ·
        refine ⟨49935762907932865297490851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66581017210577153729987801 49935762907932865297490851)
        ·
          refine ⟨74903644361899297946236277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49935762907932865297490851 74903644361899297946236277)
          ·
            refine ⟨7022216658928059182459651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74903644361899297946236277 7022216658928059182459651)
            ·
              refine ⟨10533324988392088773689477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7022216658928059182459651 10533324988392088773689477)
              ·
                refine ⟨1974998435323516645066777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10533324988392088773689477 1974998435323516645066777)
                ·
                  refine ⟨1481248826492637483800083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974998435323516645066777 1481248826492637483800083)
                  ·
                    refine ⟨2221873239738956225700125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1481248826492637483800083 2221873239738956225700125)
                    ·
                      refine ⟨833202464902108584637547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2221873239738956225700125 833202464902108584637547)
                      ·
                        rfl

theorem cell23_1622656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_1622656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622656 prefixEnd_1622656 := by exact prefixLift 1622656
  have htrace : WordTrace (prefixWord ++ tailWord_1622656) baseStart_1622656 baseEnd_1622656 := by
    simpa [prefixWord, tailWord_1622656, baseEnd_1622656] using wordTrace_append hprefix tailTrace_1622656
  have hstable : (prefixWord ++ tailWord_1622656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622656).length < 2 ^ (prefixWord ++ tailWord_1622656).sum := by decide
  have hdescent : baseEnd_1622656 < baseStart_1622656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622719 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 7]
def baseStart_1622719 : Nat := 118140960795 + 1622719 * 2 ^ 59
def prefixEnd_1622719 : Nat := 4983230072969 + 3 ^ 40 * 1622719 * 2
def baseEnd_1622719 : Nat := 92581646020371315349973

theorem tailTrace_1622719 : CollatzResearch.WordTrace tailWord_1622719 prefixEnd_1622719 92581646020371315349973 := by
  unfold tailWord_1622719
  simp only [CollatzResearch.WordTrace]
  refine ⟨59185424208173676186199211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39456949472115784124132807 59185424208173676186199211)
  ·
    refine ⟨88778136312260514279298817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59185424208173676186199211 88778136312260514279298817)
    ·
      refine ⟨66583602234195385709474113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88778136312260514279298817 66583602234195385709474113)
      ·
        refine ⟨49937701675646539282105585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66583602234195385709474113 49937701675646539282105585)
        ·
          refine ⟨37453276256734904461579189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49937701675646539282105585 37453276256734904461579189)
          ·
            refine ⟨3511244649068897293273049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37453276256734904461579189 3511244649068897293273049)
            ·
              refine ⟨2633433486801672969954787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511244649068897293273049 2633433486801672969954787)
              ·
                refine ⟨3950150230202509454932181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633433486801672969954787 3950150230202509454932181)
                ·
                  refine ⟨92581646020371315349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3950150230202509454932181 92581646020371315349973)
                  ·
                    rfl

theorem cell23_1622719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 7].length) (baseStart_1622719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622719 prefixEnd_1622719 := by exact prefixLift 1622719
  have htrace : WordTrace (prefixWord ++ tailWord_1622719) baseStart_1622719 baseEnd_1622719 := by
    simpa [prefixWord, tailWord_1622719, baseEnd_1622719] using wordTrace_append hprefix tailTrace_1622719
  have hstable : (prefixWord ++ tailWord_1622719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622719).length < 2 ^ (prefixWord ++ tailWord_1622719).sum := by decide
  have hdescent : baseEnd_1622719 < baseStart_1622719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622753 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 5]
def baseStart_1622753 : Nat := 118140960795 + 1622753 * 2 ^ 59
def prefixEnd_1622753 : Nat := 4983230072969 + 3 ^ 40 * 1622753 * 2
def baseEnd_1622753 : Nat := 92583585836177189458289

theorem tailTrace_1622753 : CollatzResearch.WordTrace tailWord_1622753 prefixEnd_1622753 92583585836177189458289 := by
  unfold tailWord_1622753
  simp only [CollatzResearch.WordTrace]
  refine ⟨59186664290050499992936913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39457776193366999995291275 59186664290050499992936913)
  ·
    refine ⟨44389998217537874994702685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59186664290050499992936913 44389998217537874994702685)
    ·
      refine ⟨16646249331576703123013507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44389998217537874994702685 16646249331576703123013507)
      ·
        refine ⟨24969373997365054684520261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16646249331576703123013507 24969373997365054684520261)
        ·
          refine ⟨4681757624505947753347549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24969373997365054684520261 4681757624505947753347549)
          ·
            refine ⟨1755659109189730407505331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4681757624505947753347549 1755659109189730407505331)
            ·
              refine ⟨2633488663784595611257997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755659109189730407505331 2633488663784595611257997)
              ·
                refine ⟨987558248919223354221749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2633488663784595611257997 987558248919223354221749)
                ·
                  refine ⟨92583585836177189458289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987558248919223354221749 92583585836177189458289)
                  ·
                    rfl

theorem cell23_1622753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 5].length) (baseStart_1622753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622753 prefixEnd_1622753 := by exact prefixLift 1622753
  have htrace : WordTrace (prefixWord ++ tailWord_1622753) baseStart_1622753 baseEnd_1622753 := by
    simpa [prefixWord, tailWord_1622753, baseEnd_1622753] using wordTrace_append hprefix tailTrace_1622753
  have hstable : (prefixWord ++ tailWord_1622753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622753).length < 2 ^ (prefixWord ++ tailWord_1622753).sum := by decide
  have hdescent : baseEnd_1622753 < baseStart_1622753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622766 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_1622766 : Nat := 118140960795 + 1622766 * 2 ^ 59
def prefixEnd_1622766 : Nat := 4983230072969 + 3 ^ 40 * 1622766 * 2
def baseEnd_1622766 : Nat := 277752982591367718087347

theorem tailTrace_1622766 : CollatzResearch.WordTrace tailWord_1622766 prefixEnd_1622766 277752982591367718087347 := by
  unfold tailWord_1622766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398392304875425401645019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39458092292668935475440101 7398392304875425401645019)
  ·
    refine ⟨11097588457313138102467529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398392304875425401645019 11097588457313138102467529)
    ·
      refine ⟨8323191342984853576850647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11097588457313138102467529 8323191342984853576850647)
      ·
        refine ⟨12484787014477280365275971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323191342984853576850647 12484787014477280365275971)
        ·
          refine ⟨18727180521715920547913957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12484787014477280365275971 18727180521715920547913957)
          ·
            refine ⟨3511346347821735102733867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18727180521715920547913957 3511346347821735102733867)
            ·
              refine ⟨5267019521732602654100801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511346347821735102733867 5267019521732602654100801)
              ·
                refine ⟨3950264641299451990575601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267019521732602654100801 3950264641299451990575601)
                ·
                  refine ⟨2962698480974588992931701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950264641299451990575601 2962698480974588992931701)
                  ·
                    refine ⟨277752982591367718087347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2962698480974588992931701 277752982591367718087347)
                    ·
                      rfl

theorem cell23_1622766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_1622766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622766 prefixEnd_1622766 := by exact prefixLift 1622766
  have htrace : WordTrace (prefixWord ++ tailWord_1622766) baseStart_1622766 baseEnd_1622766 := by
    simpa [prefixWord, tailWord_1622766, baseEnd_1622766] using wordTrace_append hprefix tailTrace_1622766
  have hstable : (prefixWord ++ tailWord_1622766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622766).length < 2 ^ (prefixWord ++ tailWord_1622766).sum := by decide
  have hdescent : baseEnd_1622766 < baseStart_1622766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622789 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_1622789 : Nat := 118140960795 + 1622789 * 2 ^ 59
def prefixEnd_1622789 : Nat := 4983230072969 + 3 ^ 40 * 1622789 * 2
def baseEnd_1622789 : Nat := 833270757829156564274435

theorem tailTrace_1622789 : CollatzResearch.WordTrace tailWord_1622789 prefixEnd_1622789 833270757829156564274435 := by
  unfold tailWord_1622789
  simp only [CollatzResearch.WordTrace]
  refine ⟨59187977317920078141247421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39458651545280052094164947 59187977317920078141247421)
  ·
    refine ⟨22195491494220029302967783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59187977317920078141247421 22195491494220029302967783)
    ·
      refine ⟨33293237241330043954451675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22195491494220029302967783 33293237241330043954451675)
      ·
        refine ⟨49939855861995065931677513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33293237241330043954451675 49939855861995065931677513)
        ·
          refine ⟨37454891896496299448758135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49939855861995065931677513 37454891896496299448758135)
          ·
            refine ⟨56182337844744449173137203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37454891896496299448758135 56182337844744449173137203)
            ·
              refine ⟨84273506767116673759705805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56182337844744449173137203 84273506767116673759705805)
              ·
                refine ⟨31602565037668752659889677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84273506767116673759705805 31602565037668752659889677)
                ·
                  refine ⟨11850961889125782247458629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31602565037668752659889677 11850961889125782247458629)
                  ·
                    refine ⟨2222055354211084171398493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11850961889125782247458629 2222055354211084171398493)
                    ·
                      refine ⟨833270757829156564274435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222055354211084171398493 833270757829156564274435)
                      ·
                        rfl

theorem cell23_1622789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_1622789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622789 prefixEnd_1622789 := by exact prefixLift 1622789
  have htrace : WordTrace (prefixWord ++ tailWord_1622789) baseStart_1622789 baseEnd_1622789 := by
    simpa [prefixWord, tailWord_1622789, baseEnd_1622789] using wordTrace_append hprefix tailTrace_1622789
  have hstable : (prefixWord ++ tailWord_1622789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622789).length < 2 ^ (prefixWord ++ tailWord_1622789).sum := by decide
  have hdescent : baseEnd_1622789 < baseStart_1622789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622839 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 5, 5]
def baseStart_1622839 : Nat := 118140960795 + 1622839 * 2 ^ 59
def prefixEnd_1622839 : Nat := 4983230072969 + 3 ^ 40 * 1622839 * 2
def baseEnd_1622839 : Nat := 277765477287293789549735

theorem tailTrace_1622839 : CollatzResearch.WordTrace tailWord_1622839 prefixEnd_1622839 277765477287293789549735 := by
  unfold tailWord_1622839
  simp only [CollatzResearch.WordTrace]
  refine ⟨59189800967738936680567571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39459867311825957787045047 59189800967738936680567571)
  ·
    refine ⟨88784701451608405020851357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59189800967738936680567571 88784701451608405020851357)
    ·
      refine ⟨33294263044353151882819259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88784701451608405020851357 33294263044353151882819259)
      ·
        refine ⟨49941394566529727824228889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33294263044353151882819259 49941394566529727824228889)
        ·
          refine ⟨37456045924897295868171667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49941394566529727824228889 37456045924897295868171667)
          ·
            refine ⟨56184068887345943802257501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37456045924897295868171667 56184068887345943802257501)
            ·
              refine ⟨21069025832754728925846563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56184068887345943802257501 21069025832754728925846563)
              ·
                refine ⟨31603538749132093388769845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21069025832754728925846563 31603538749132093388769845)
                ·
                  refine ⟨2962831757731133755197173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31603538749132093388769845 2962831757731133755197173)
                  ·
                    refine ⟨277765477287293789549735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2962831757731133755197173 277765477287293789549735)
                    ·
                      rfl

theorem cell23_1622839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_1622839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622839 prefixEnd_1622839 := by exact prefixLift 1622839
  have htrace : WordTrace (prefixWord ++ tailWord_1622839) baseStart_1622839 baseEnd_1622839 := by
    simpa [prefixWord, tailWord_1622839, baseEnd_1622839] using wordTrace_append hprefix tailTrace_1622839
  have hstable : (prefixWord ++ tailWord_1622839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622839).length < 2 ^ (prefixWord ++ tailWord_1622839).sum := by decide
  have hdescent : baseEnd_1622839 < baseStart_1622839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622854 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1622854 : Nat := 118140960795 + 1622854 * 2 ^ 59
def prefixEnd_1622854 : Nat := 4983230072969 + 3 ^ 40 * 1622854 * 2
def baseEnd_1622854 : Nat := 833304134071698809961637

theorem tailTrace_1622854 : CollatzResearch.WordTrace tailWord_1622854 prefixEnd_1622854 833304134071698809961637 := by
  unfold tailWord_1622854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849698376958893570073863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39460232041789729494909077 1849698376958893570073863)
  ·
    refine ⟨2774547565438340355110795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1849698376958893570073863 2774547565438340355110795)
    ·
      refine ⟨4161821348157510532666193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774547565438340355110795 4161821348157510532666193)
      ·
        refine ⟨3121366011118132899499645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4161821348157510532666193 3121366011118132899499645)
        ·
          refine ⟨1170512254169299837312367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3121366011118132899499645 1170512254169299837312367)
          ·
            refine ⟨1755768381253949755968551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170512254169299837312367 1755768381253949755968551)
            ·
              refine ⟨2633652571880924633952827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755768381253949755968551 2633652571880924633952827)
              ·
                refine ⟨3950478857821386950929241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633652571880924633952827 3950478857821386950929241)
                ·
                  refine ⟨2962859143366040213196931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950478857821386950929241 2962859143366040213196931)
                  ·
                    refine ⟨4444288715049060319795397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2962859143366040213196931 4444288715049060319795397)
                    ·
                      refine ⟨833304134071698809961637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4444288715049060319795397 833304134071698809961637)
                      ·
                        rfl

theorem cell23_1622854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1622854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622854 prefixEnd_1622854 := by exact prefixLift 1622854
  have htrace : WordTrace (prefixWord ++ tailWord_1622854) baseStart_1622854 baseEnd_1622854 := by
    simpa [prefixWord, tailWord_1622854, baseEnd_1622854] using wordTrace_append hprefix tailTrace_1622854
  have hstable : (prefixWord ++ tailWord_1622854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622854).length < 2 ^ (prefixWord ++ tailWord_1622854).sum := by decide
  have hdescent : baseEnd_1622854 < baseStart_1622854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622856 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 1, 5]
def baseStart_1622856 : Nat := 118140960795 + 1622856 * 2 ^ 59
def prefixEnd_1622856 : Nat := 4983230072969 + 3 ^ 40 * 1622856 * 2
def baseEnd_1622856 : Nat := 277768387011002600712209

theorem tailTrace_1622856 : CollatzResearch.WordTrace tailWord_1622856 prefixEnd_1622856 277768387011002600712209 := by
  unfold tailWord_1622856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29595210504338674291968211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39460280672451565722624281 29595210504338674291968211)
  ·
    refine ⟨44392815756508011437952317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29595210504338674291968211 44392815756508011437952317)
    ·
      refine ⟨16647305908690504289232119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44392815756508011437952317 16647305908690504289232119)
      ·
        refine ⟨24970958863035756433848179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16647305908690504289232119 24970958863035756433848179)
        ·
          refine ⟨37456438294553634650772269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24970958863035756433848179 37456438294553634650772269)
          ·
            refine ⟨14046164360457612994039601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37456438294553634650772269 14046164360457612994039601)
            ·
              refine ⟨10534623270343209745529701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14046164360457612994039601 10534623270343209745529701)
              ·
                refine ⟨1975241863189351827286819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10534623270343209745529701 1975241863189351827286819)
                ·
                  refine ⟨2962862794784027740930229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975241863189351827286819 2962862794784027740930229)
                  ·
                    refine ⟨277768387011002600712209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2962862794784027740930229 277768387011002600712209)
                    ·
                      rfl

theorem cell23_1622856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_1622856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622856 prefixEnd_1622856 := by exact prefixLift 1622856
  have htrace : WordTrace (prefixWord ++ tailWord_1622856) baseStart_1622856 baseEnd_1622856 := by
    simpa [prefixWord, tailWord_1622856, baseEnd_1622856] using wordTrace_append hprefix tailTrace_1622856
  have hstable : (prefixWord ++ tailWord_1622856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622856).length < 2 ^ (prefixWord ++ tailWord_1622856).sum := by decide
  have hdescent : baseEnd_1622856 < baseStart_1622856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622873 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 1, 5]
def baseStart_1622873 : Nat := 118140960795 + 1622873 * 2 ^ 59
def prefixEnd_1622873 : Nat := 4983230072969 + 3 ^ 40 * 1622873 * 2
def baseEnd_1622873 : Nat := 277771296734711411874683

theorem tailTrace_1622873 : CollatzResearch.WordTrace tailWord_1622873 prefixEnd_1622873 277771296734711411874683 := by
  unfold tailWord_1622873
  simp only [CollatzResearch.WordTrace]
  refine ⟨59191041049615760487305273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39460694033077173658203515 59191041049615760487305273)
  ·
    refine ⟨44393280787211820365478955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59191041049615760487305273 44393280787211820365478955)
    ·
      refine ⟨66589921180817730548218433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44393280787211820365478955 66589921180817730548218433)
      ·
        refine ⟨49942440885613297911163825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66589921180817730548218433 49942440885613297911163825)
        ·
          refine ⟨37456830664209973433372869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49942440885613297911163825 37456830664209973433372869)
          ·
            refine ⟨7023155749539370018757413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37456830664209973433372869 7023155749539370018757413)
            ·
              refine ⟨1316841703038631878517015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7023155749539370018757413 1316841703038631878517015)
              ·
                refine ⟨1975262554557947817775523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316841703038631878517015 1975262554557947817775523)
                ·
                  refine ⟨2962893831836921726663285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975262554557947817775523 2962893831836921726663285)
                  ·
                    refine ⟨277771296734711411874683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2962893831836921726663285 277771296734711411874683)
                    ·
                      rfl

theorem cell23_1622873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 5].length) (baseStart_1622873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622873 prefixEnd_1622873 := by exact prefixLift 1622873
  have htrace : WordTrace (prefixWord ++ tailWord_1622873) baseStart_1622873 baseEnd_1622873 := by
    simpa [prefixWord, tailWord_1622873, baseEnd_1622873] using wordTrace_append hprefix tailTrace_1622873
  have hstable : (prefixWord ++ tailWord_1622873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622873).length < 2 ^ (prefixWord ++ tailWord_1622873).sum := by decide
  have hdescent : baseEnd_1622873 < baseStart_1622873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622889 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_1622889 : Nat := 118140960795 + 1622889 * 2 ^ 59
def prefixEnd_1622889 : Nat := 4983230072969 + 3 ^ 40 * 1622889 * 2
def baseEnd_1622889 : Nat := 833322105894606173023975

theorem tailTrace_1622889 : CollatzResearch.WordTrace tailWord_1622889 prefixEnd_1622889 833322105894606173023975 := by
  unfold tailWord_1622889
  simp only [CollatzResearch.WordTrace]
  refine ⟨59191624617557795219887721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39461083078371863479925147 59191624617557795219887721)
  ·
    refine ⟨44393718463168346414915791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59191624617557795219887721 44393718463168346414915791)
    ·
      refine ⟨66590577694752519622373687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44393718463168346414915791 66590577694752519622373687)
      ·
        refine ⟨99885866542128779433560531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66590577694752519622373687 99885866542128779433560531)
        ·
          refine ⟨149828799813193169150340797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99885866542128779433560531 149828799813193169150340797)
          ·
            refine ⟨56185799929947438431377799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149828799813193169150340797 56185799929947438431377799)
            ·
              refine ⟨84278699894921157647066699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56185799929947438431377799 84278699894921157647066699)
              ·
                refine ⟨126418049842381736470600049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84278699894921157647066699 126418049842381736470600049)
                ·
                  refine ⟨94813537381786302352950037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126418049842381736470600049 94813537381786302352950037)
                  ·
                    refine ⟨4444384564771232922794533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94813537381786302352950037 4444384564771232922794533)
                    ·
                      refine ⟨833322105894606173023975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4444384564771232922794533 833322105894606173023975)
                      ·
                        rfl

theorem cell23_1622889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_1622889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622889 prefixEnd_1622889 := by exact prefixLift 1622889
  have htrace : WordTrace (prefixWord ++ tailWord_1622889) baseStart_1622889 baseEnd_1622889 := by
    simpa [prefixWord, tailWord_1622889, baseEnd_1622889] using wordTrace_append hprefix tailTrace_1622889
  have hstable : (prefixWord ++ tailWord_1622889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622889).length < 2 ^ (prefixWord ++ tailWord_1622889).sum := by decide
  have hdescent : baseEnd_1622889 < baseStart_1622889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622896 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_1622896 : Nat := 118140960795 + 1622896 * 2 ^ 59
def prefixEnd_1622896 : Nat := 4983230072969 + 3 ^ 40 * 1622896 * 2
def baseEnd_1622896 : Nat := 833325700259187645636443

theorem tailTrace_1622896 : CollatzResearch.WordTrace tailWord_1622896 prefixEnd_1622896 833325700259187645636443 := by
  unfold tailWord_1622896
  simp only [CollatzResearch.WordTrace]
  refine ⟨29595939964266217707696271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39461253285688290276928361 29595939964266217707696271)
  ·
    refine ⟨44393909946399326561544407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29595939964266217707696271 44393909946399326561544407)
    ·
      refine ⟨66590864919598989842316611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44393909946399326561544407 66590864919598989842316611)
      ·
        refine ⟨99886297379398484763474917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66590864919598989842316611 99886297379398484763474917)
        ·
          refine ⟨18728680758637215893151547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99886297379398484763474917 18728680758637215893151547)
          ·
            refine ⟨28093021137955823839727321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18728680758637215893151547 28093021137955823839727321)
            ·
              refine ⟨21069765853466867879795491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28093021137955823839727321 21069765853466867879795491)
              ·
                refine ⟨31604648780200301819693237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21069765853466867879795491 31604648780200301819693237)
                ·
                  refine ⟨2962935823143778295596241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31604648780200301819693237 2962935823143778295596241)
                  ·
                    refine ⟨2222201867357833721697181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2962935823143778295596241 2222201867357833721697181)
                    ·
                      refine ⟨833325700259187645636443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222201867357833721697181 833325700259187645636443)
                      ·
                        rfl

theorem cell23_1622896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_1622896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622896 prefixEnd_1622896 := by exact prefixLift 1622896
  have htrace : WordTrace (prefixWord ++ tailWord_1622896) baseStart_1622896 baseEnd_1622896 := by
    simpa [prefixWord, tailWord_1622896, baseEnd_1622896] using wordTrace_append hprefix tailTrace_1622896
  have hstable : (prefixWord ++ tailWord_1622896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622896).length < 2 ^ (prefixWord ++ tailWord_1622896).sum := by decide
  have hdescent : baseEnd_1622896 < baseStart_1622896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622929 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 9]
def baseStart_1622929 : Nat := 118140960795 + 1622929 * 2 ^ 59
def prefixEnd_1622929 : Nat := 4983230072969 + 3 ^ 40 * 1622929 * 2
def baseEnd_1622929 : Nat := 277780881706928672174597

theorem tailTrace_1622929 : CollatzResearch.WordTrace tailWord_1622929 prefixEnd_1622929 277780881706928672174597 := by
  unfold tailWord_1622929
  simp only [CollatzResearch.WordTrace]
  refine ⟨59193083537412882051343841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39462055691608588034229227 59193083537412882051343841)
  ·
    refine ⟨44394812653059661538507881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59193083537412882051343841 44394812653059661538507881)
    ·
      refine ⟨33296109489794746153880911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44394812653059661538507881 33296109489794746153880911)
      ·
        refine ⟨49944164234692119230821367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33296109489794746153880911 49944164234692119230821367)
        ·
          refine ⟨74916246352038178846232051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49944164234692119230821367 74916246352038178846232051)
          ·
            refine ⟨112374369528057268269348077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74916246352038178846232051 112374369528057268269348077)
            ·
              refine ⟨42140388573021475601005529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112374369528057268269348077 42140388573021475601005529)
              ·
                refine ⟨31605291429766106700754147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42140388573021475601005529 31605291429766106700754147)
                ·
                  refine ⟨47407937144649160051131221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31605291429766106700754147 47407937144649160051131221)
                  ·
                    refine ⟨277780881706928672174597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47407937144649160051131221 277780881706928672174597)
                    ·
                      rfl

theorem cell23_1622929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_1622929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622929 prefixEnd_1622929 := by exact prefixLift 1622929
  have htrace : WordTrace (prefixWord ++ tailWord_1622929) baseStart_1622929 baseEnd_1622929 := by
    simpa [prefixWord, tailWord_1622929, baseEnd_1622929] using wordTrace_append hprefix tailTrace_1622929
  have hstable : (prefixWord ++ tailWord_1622929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622929).length < 2 ^ (prefixWord ++ tailWord_1622929).sum := by decide
  have hdescent : baseEnd_1622929 < baseStart_1622929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622930 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1622930 : Nat := 118140960795 + 1622930 * 2 ^ 59
def prefixEnd_1622930 : Nat := 4983230072969 + 3 ^ 40 * 1622930 * 2
def baseEnd_1622930 : Nat := 833343158601440512611287

theorem tailTrace_1622930 : CollatzResearch.WordTrace tailWord_1622930 prefixEnd_1622930 833343158601440512611287 := by
  unfold tailWord_1622930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798280002602314805532561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39462080006939506148086829 14798280002602314805532561)
  ·
    refine ⟨11098710001951736104149421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14798280002602314805532561 11098710001951736104149421)
    ·
      refine ⟨4162016250731901039056033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11098710001951736104149421 4162016250731901039056033)
      ·
        refine ⟨3121512188048925779292025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4162016250731901039056033 3121512188048925779292025)
        ·
          refine ⟨2341134141036694334469019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121512188048925779292025 2341134141036694334469019)
          ·
            refine ⟨3511701211555041501703529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341134141036694334469019 3511701211555041501703529)
            ·
              refine ⟨2633775908666281126277647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511701211555041501703529 2633775908666281126277647)
              ·
                refine ⟨3950663862999421689416471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633775908666281126277647 3950663862999421689416471)
                ·
                  refine ⟨5925995794499132534124707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950663862999421689416471 5925995794499132534124707)
                  ·
                    refine ⟨8888993691748698801187061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5925995794499132534124707 8888993691748698801187061)
                    ·
                      refine ⟨833343158601440512611287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8888993691748698801187061 833343158601440512611287)
                      ·
                        rfl

theorem cell23_1622930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1622930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622930 prefixEnd_1622930 := by exact prefixLift 1622930
  have htrace : WordTrace (prefixWord ++ tailWord_1622930) baseStart_1622930 baseEnd_1622930 := by
    simpa [prefixWord, tailWord_1622930, baseEnd_1622930] using wordTrace_append hprefix tailTrace_1622930
  have hstable : (prefixWord ++ tailWord_1622930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622930).length < 2 ^ (prefixWord ++ tailWord_1622930).sum := by decide
  have hdescent : baseEnd_1622930 < baseStart_1622930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622953 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 3, 3, 2]
def baseStart_1622953 : Nat := 118140960795 + 1622953 * 2 ^ 59
def prefixEnd_1622953 : Nat := 4983230072969 + 3 ^ 40 * 1622953 * 2
def baseEnd_1622953 : Nat := 833354968656493922623681

theorem tailTrace_1622953 : CollatzResearch.WordTrace tailWord_1622953 prefixEnd_1622953 833354968656493922623681 := by
  unfold tailWord_1622953
  simp only [CollatzResearch.WordTrace]
  refine ⟨59193958889325934150217513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39462639259550622766811675 59193958889325934150217513)
  ·
    refine ⟨44395469166994450612663135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59193958889325934150217513 44395469166994450612663135)
    ·
      refine ⟨66593203750491675918994703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44395469166994450612663135 66593203750491675918994703)
      ·
        refine ⟨99889805625737513878492055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66593203750491675918994703 99889805625737513878492055)
        ·
          refine ⟨149834708438606270817738083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99889805625737513878492055 149834708438606270817738083)
          ·
            refine ⟨224752062657909406226607125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149834708438606270817738083 224752062657909406226607125)
            ·
              refine ⟨10535252937089503416872209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224752062657909406226607125 10535252937089503416872209)
              ·
                refine ⟨7901439702817127562654157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10535252937089503416872209 7901439702817127562654157)
                ·
                  refine ⟨2963039888556422835995309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7901439702817127562654157 2963039888556422835995309)
                  ·
                    refine ⟨1111139958208658563498241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963039888556422835995309 1111139958208658563498241)
                    ·
                      refine ⟨833354968656493922623681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111139958208658563498241 833354968656493922623681)
                      ·
                        rfl

theorem cell23_1622953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 3, 2].length) (baseStart_1622953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622953 prefixEnd_1622953 := by exact prefixLift 1622953
  have htrace : WordTrace (prefixWord ++ tailWord_1622953) baseStart_1622953 baseEnd_1622953 := by
    simpa [prefixWord, tailWord_1622953, baseEnd_1622953] using wordTrace_append hprefix tailTrace_1622953
  have hstable : (prefixWord ++ tailWord_1622953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622953).length < 2 ^ (prefixWord ++ tailWord_1622953).sum := by decide
  have hdescent : baseEnd_1622953 < baseStart_1622953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622964 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1622964 : Nat := 118140960795 + 1622964 * 2 ^ 59
def prefixEnd_1622964 : Nat := 4983230072969 + 3 ^ 40 * 1622964 * 2
def baseEnd_1622964 : Nat := 833360616943693379586131

theorem tailTrace_1622964 : CollatzResearch.WordTrace tailWord_1622964 prefixEnd_1622964 833360616943693379586131 := by
  unfold tailWord_1622964
  simp only [CollatzResearch.WordTrace]
  refine ⟨29597180046143041514433973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39462906728190722019245297 29597180046143041514433973)
  ·
    refine ⟨2774735629325910141978185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29597180046143041514433973 2774735629325910141978185)
    ·
      refine ⟨2081051721994432606483639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2774735629325910141978185 2081051721994432606483639)
      ·
        refine ⟨3121577582991648909725459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081051721994432606483639 3121577582991648909725459)
        ·
          refine ⟨4682366374487473364588189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121577582991648909725459 4682366374487473364588189)
          ·
            refine ⟨1755887390432802511720571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4682366374487473364588189 1755887390432802511720571)
            ·
              refine ⟨2633831085649203767580857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755887390432802511720571 2633831085649203767580857)
              ·
                refine ⟨1975373314236902825685643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633831085649203767580857 1975373314236902825685643)
                ·
                  refine ⟨2963059971355354238528465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975373314236902825685643 2963059971355354238528465)
                  ·
                    refine ⟨2222294978516515678896349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963059971355354238528465 2222294978516515678896349)
                    ·
                      refine ⟨833360616943693379586131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222294978516515678896349 833360616943693379586131)
                      ·
                        rfl

theorem cell23_1622964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1622964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622964 prefixEnd_1622964 := by exact prefixLift 1622964
  have htrace : WordTrace (prefixWord ++ tailWord_1622964) baseStart_1622964 baseEnd_1622964 := by
    simpa [prefixWord, tailWord_1622964, baseEnd_1622964] using wordTrace_append hprefix tailTrace_1622964
  have hstable : (prefixWord ++ tailWord_1622964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622964).length < 2 ^ (prefixWord ++ tailWord_1622964).sum := by decide
  have hdescent : baseEnd_1622964 < baseStart_1622964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622983 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_1622983 : Nat := 118140960795 + 1622983 * 2 ^ 59
def prefixEnd_1622983 : Nat := 4983230072969 + 3 ^ 40 * 1622983 * 2
def baseEnd_1622983 : Nat := 833370373076128805248543

theorem tailTrace_1622983 : CollatzResearch.WordTrace tailWord_1622983 prefixEnd_1622983 833370373076128805248543 := by
  unfold tailWord_1622983
  simp only [CollatzResearch.WordTrace]
  refine ⟨59195053079217249273809603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39463368719478166182539735 59195053079217249273809603)
  ·
    refine ⟨88792579618825873910714405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59195053079217249273809603 88792579618825873910714405)
    ·
      refine ⟨16648608678529851358258951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88792579618825873910714405 16648608678529851358258951)
      ·
        refine ⟨24972913017794777037388427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16648608678529851358258951 24972913017794777037388427)
        ·
          refine ⟨37459369526692165556082641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24972913017794777037388427 37459369526692165556082641)
          ·
            refine ⟨28094527145019124167061981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37459369526692165556082641 28094527145019124167061981)
            ·
              refine ⟨10535447679382171562648243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28094527145019124167061981 10535447679382171562648243)
              ·
                refine ⟨15803171519073257343972365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10535447679382171562648243 15803171519073257343972365)
                ·
                  refine ⟨5926189319652471503989637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15803171519073257343972365 5926189319652471503989637)
                  ·
                    refine ⟨1111160497434838406998057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926189319652471503989637 1111160497434838406998057)
                    ·
                      refine ⟨833370373076128805248543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111160497434838406998057 833370373076128805248543)
                      ·
                        rfl

theorem cell23_1622983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_1622983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622983 prefixEnd_1622983 := by exact prefixLift 1622983
  have htrace : WordTrace (prefixWord ++ tailWord_1622983) baseStart_1622983 baseEnd_1622983 := by
    simpa [prefixWord, tailWord_1622983, baseEnd_1622983] using wordTrace_append hprefix tailTrace_1622983
  have hstable : (prefixWord ++ tailWord_1622983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622983).length < 2 ^ (prefixWord ++ tailWord_1622983).sum := by decide
  have hdescent : baseEnd_1622983 < baseStart_1622983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622987 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 1, 3, 2]
def baseStart_1622987 : Nat := 118140960795 + 1622987 * 2 ^ 59
def prefixEnd_1622987 : Nat := 4983230072969 + 3 ^ 40 * 1622987 * 2
def baseEnd_1622987 : Nat := 833372426998746789598525

theorem tailTrace_1622987 : CollatzResearch.WordTrace tailWord_1622987 prefixEnd_1622987 833372426998746789598525 := by
  unfold tailWord_1622987
  simp only [CollatzResearch.WordTrace]
  refine ⟨59195198971202757956955215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39463465980801838637970143 59195198971202757956955215)
  ·
    refine ⟨88792798456804136935432823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59195198971202757956955215 88792798456804136935432823)
    ·
      refine ⟨133189197685206205403149235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88792798456804136935432823 133189197685206205403149235)
      ·
        refine ⟨199783796527809308104723853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133189197685206205403149235 199783796527809308104723853)
        ·
          refine ⟨74918923697928490539271445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199783796527809308104723853 74918923697928490539271445)
          ·
            refine ⟨3511824548340397994028349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74918923697928490539271445 3511824548340397994028349)
            ·
              refine ⟨1316934205627649247760631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3511824548340397994028349 1316934205627649247760631)
              ·
                refine ⟨1975401308441473871640947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316934205627649247760631 1975401308441473871640947)
                ·
                  refine ⟨2963101962662210807461421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975401308441473871640947 2963101962662210807461421)
                  ·
                    refine ⟨1111163235998329052798033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963101962662210807461421 1111163235998329052798033)
                    ·
                      refine ⟨833372426998746789598525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111163235998329052798033 833372426998746789598525)
                      ·
                        rfl

theorem cell23_1622987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 1, 3, 2].length) (baseStart_1622987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1622987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1622987 prefixEnd_1622987 := by exact prefixLift 1622987
  have htrace : WordTrace (prefixWord ++ tailWord_1622987) baseStart_1622987 baseEnd_1622987 := by
    simpa [prefixWord, tailWord_1622987, baseEnd_1622987] using wordTrace_append hprefix tailTrace_1622987
  have hstable : (prefixWord ++ tailWord_1622987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622987).length < 2 ^ (prefixWord ++ tailWord_1622987).sum := by decide
  have hdescent : baseEnd_1622987 < baseStart_1622987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623010 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1623010 : Nat := 118140960795 + 1623010 * 2 ^ 59
def prefixEnd_1623010 : Nat := 4983230072969 + 3 ^ 40 * 1623010 * 2
def baseEnd_1623010 : Nat := 277794745684600066536973

theorem tailTrace_1623010 : CollatzResearch.WordTrace tailWord_1623010 prefixEnd_1623010 277794745684600066536973 := by
  unfold tailWord_1623010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799009462529858221260621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39464025233412955256694989 14799009462529858221260621)
  ·
    refine ⟨5549628548448696832972733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14799009462529858221260621 5549628548448696832972733)
    ·
      refine ⟨2081110705668261312364775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5549628548448696832972733 2081110705668261312364775)
      ·
        refine ⟨3121666058502391968547163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081110705668261312364775 3121666058502391968547163)
        ·
          refine ⟨4682499087753587952820745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121666058502391968547163 4682499087753587952820745)
          ·
            refine ⟨3511874315815190964615559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682499087753587952820745 3511874315815190964615559)
            ·
              refine ⟨5267811473722786446923339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511874315815190964615559 5267811473722786446923339)
              ·
                refine ⟨7901717210584179670385009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267811473722786446923339 7901717210584179670385009)
                ·
                  refine ⟨5926287907938134752788757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7901717210584179670385009 5926287907938134752788757)
                  ·
                    refine ⟨277794745684600066536973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5926287907938134752788757 277794745684600066536973)
                    ·
                      rfl

theorem cell23_1623010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1623010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623010 prefixEnd_1623010 := by exact prefixLift 1623010
  have htrace : WordTrace (prefixWord ++ tailWord_1623010) baseStart_1623010 baseEnd_1623010 := by
    simpa [prefixWord, tailWord_1623010, baseEnd_1623010] using wordTrace_append hprefix tailTrace_1623010
  have hstable : (prefixWord ++ tailWord_1623010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623010).length < 2 ^ (prefixWord ++ tailWord_1623010).sum := by decide
  have hdescent : baseEnd_1623010 < baseStart_1623010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623038 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1623038 : Nat := 118140960795 + 1623038 * 2 ^ 59
def prefixEnd_1623038 : Nat := 4983230072969 + 3 ^ 40 * 1623038 * 2
def baseEnd_1623038 : Nat := 833398614512126090060791

theorem tailTrace_1623038 : CollatzResearch.WordTrace tailWord_1623038 prefixEnd_1623038 833398614512126090060791 := by
  unfold tailWord_1623038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7399632386752249208382721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39464706062678662444707845 7399632386752249208382721)
  ·
    refine ⟨5549724290064186906287041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7399632386752249208382721 5549724290064186906287041)
    ·
      refine ⟨4162293217548140179715281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5549724290064186906287041 4162293217548140179715281)
      ·
        refine ⟨3121719913161105134786461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4162293217548140179715281 3121719913161105134786461)
        ·
          refine ⟨1170644967435414425544923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3121719913161105134786461 1170644967435414425544923)
          ·
            refine ⟨1755967451153121638317385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170644967435414425544923 1755967451153121638317385)
            ·
              refine ⟨1316975588364841228738039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755967451153121638317385 1316975588364841228738039)
              ·
                refine ⟨1975463382547261843107059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316975588364841228738039 1975463382547261843107059)
                ·
                  refine ⟨2963195073820892764660589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975463382547261843107059 2963195073820892764660589)
                  ·
                    refine ⟨1111198152682834786747721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963195073820892764660589 1111198152682834786747721)
                    ·
                      refine ⟨833398614512126090060791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111198152682834786747721 833398614512126090060791)
                      ·
                        rfl

theorem cell23_1623038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1623038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623038 prefixEnd_1623038 := by exact prefixLift 1623038
  have htrace : WordTrace (prefixWord ++ tailWord_1623038) baseStart_1623038 baseEnd_1623038 := by
    simpa [prefixWord, tailWord_1623038, baseEnd_1623038] using wordTrace_append hprefix tailTrace_1623038
  have hstable : (prefixWord ++ tailWord_1623038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623038).length < 2 ^ (prefixWord ++ tailWord_1623038).sum := by decide
  have hdescent : baseEnd_1623038 < baseStart_1623038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623056 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_1623056 : Nat := 118140960795 + 1623056 * 2 ^ 59
def prefixEnd_1623056 : Nat := 4983230072969 + 3 ^ 40 * 1623056 * 2
def baseEnd_1623056 : Nat := 833407857163907019635707

theorem tailTrace_1623056 : CollatzResearch.WordTrace tailWord_1623056 prefixEnd_1623056 833407857163907019635707 := by
  unfold tailWord_1623056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29598857803976391370608511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39465143738635188494144681 29598857803976391370608511)
  ·
    refine ⟨44398286705964587055912767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29598857803976391370608511 44398286705964587055912767)
    ·
      refine ⟨66597430058946880583869151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44398286705964587055912767 66597430058946880583869151)
      ·
        refine ⟨99896145088420320875803727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66597430058946880583869151 99896145088420320875803727)
        ·
          refine ⟨149844217632630481313705591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99896145088420320875803727 149844217632630481313705591)
          ·
            refine ⟨224766326448945721970558387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149844217632630481313705591 224766326448945721970558387)
            ·
              refine ⟨337149489673418582955837581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224766326448945721970558387 337149489673418582955837581)
              ·
                refine ⟨126431058627531968608439093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337149489673418582955837581 126431058627531968608439093)
                ·
                  refine ⟨11852911746331122057041165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126431058627531968608439093 11852911746331122057041165)
                  ·
                    refine ⟨4444841904874170771390437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11852911746331122057041165 4444841904874170771390437)
                    ·
                      refine ⟨833407857163907019635707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4444841904874170771390437 833407857163907019635707)
                      ·
                        rfl

theorem cell23_1623056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_1623056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623056 prefixEnd_1623056 := by exact prefixLift 1623056
  have htrace : WordTrace (prefixWord ++ tailWord_1623056) baseStart_1623056 baseEnd_1623056 := by
    simpa [prefixWord, tailWord_1623056, baseEnd_1623056] using wordTrace_append hprefix tailTrace_1623056
  have hstable : (prefixWord ++ tailWord_1623056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623056).length < 2 ^ (prefixWord ++ tailWord_1623056).sum := by decide
  have hdescent : baseEnd_1623056 < baseStart_1623056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623073 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1623073 : Nat := 118140960795 + 1623073 * 2 ^ 59
def prefixEnd_1623073 : Nat := 4983230072969 + 3 ^ 40 * 1623073 * 2
def baseEnd_1623073 : Nat := 833416586335033453123129

theorem tailTrace_1623073 : CollatzResearch.WordTrace tailWord_1623073 prefixEnd_1623073 833416586335033453123129 := by
  unfold tailWord_1623073
  simp only [CollatzResearch.WordTrace]
  refine ⟨59198335648891194644585873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39465557099260796429723915 59198335648891194644585873)
  ·
    refine ⟨44398751736668395983439405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59198335648891194644585873 44398751736668395983439405)
    ·
      refine ⟨16649531901250648493789777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44398751736668395983439405 16649531901250648493789777)
      ·
        refine ⟨12487148925937986370342333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16649531901250648493789777 12487148925937986370342333)
        ·
          refine ⟨4682680847226744888878375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12487148925937986370342333 4682680847226744888878375)
          ·
            refine ⟨7024021270840117333317563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682680847226744888878375 7024021270840117333317563)
            ·
              refine ⟨10536031906260175999976345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024021270840117333317563 10536031906260175999976345)
              ·
                refine ⟨7902023929695131999982259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10536031906260175999976345 7902023929695131999982259)
                ·
                  refine ⟨11853035894542697999973389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7902023929695131999982259 11853035894542697999973389)
                  ·
                    refine ⟨4444888460453511749990021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11853035894542697999973389 4444888460453511749990021)
                    ·
                      refine ⟨833416586335033453123129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4444888460453511749990021 833416586335033453123129)
                      ·
                        rfl

theorem cell23_1623073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1623073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623073 prefixEnd_1623073 := by exact prefixLift 1623073
  have htrace : WordTrace (prefixWord ++ tailWord_1623073) baseStart_1623073 baseEnd_1623073 := by
    simpa [prefixWord, tailWord_1623073, baseEnd_1623073] using wordTrace_append hprefix tailTrace_1623073
  have hstable : (prefixWord ++ tailWord_1623073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623073).length < 2 ^ (prefixWord ++ tailWord_1623073).sum := by decide
  have hdescent : baseEnd_1623073 < baseStart_1623073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623083 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 3, 4]
def baseStart_1623083 : Nat := 118140960795 + 1623083 * 2 ^ 59
def prefixEnd_1623083 : Nat := 4983230072969 + 3 ^ 40 * 1623083 * 2
def baseEnd_1623083 : Nat := 277807240380526137999361

theorem tailTrace_1623083 : CollatzResearch.WordTrace tailWord_1623083 prefixEnd_1623083 277807240380526137999361 := by
  unfold tailWord_1623083
  simp only [CollatzResearch.WordTrace]
  refine ⟨59198700378854966352449903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39465800252569977568299935 59198700378854966352449903)
  ·
    refine ⟨88798050568282449528674855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59198700378854966352449903 88798050568282449528674855)
    ·
      refine ⟨133197075852423674293012283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88798050568282449528674855 133197075852423674293012283)
      ·
        refine ⟨199795613778635511439518425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133197075852423674293012283 199795613778635511439518425)
        ·
          refine ⟨149846710333976633579638819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199795613778635511439518425 149846710333976633579638819)
          ·
            refine ⟨224770065500964950369458229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149846710333976633579638819 224770065500964950369458229)
            ·
              refine ⟨21072193640715464097136709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224770065500964950369458229 21072193640715464097136709)
              ·
                refine ⟨3951036307634149518213133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21072193640715464097136709 3951036307634149518213133)
                ·
                  refine ⟨1481638615362806069329925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3951036307634149518213133 1481638615362806069329925)
                  ·
                    refine ⟨277807240380526137999361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1481638615362806069329925 277807240380526137999361)
                    ·
                      rfl

theorem cell23_1623083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 4].length) (baseStart_1623083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623083 prefixEnd_1623083 := by exact prefixLift 1623083
  have htrace : WordTrace (prefixWord ++ tailWord_1623083) baseStart_1623083 baseEnd_1623083 := by
    simpa [prefixWord, tailWord_1623083, baseEnd_1623083] using wordTrace_append hprefix tailTrace_1623083
  have hstable : (prefixWord ++ tailWord_1623083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623083).length < 2 ^ (prefixWord ++ tailWord_1623083).sum := by decide
  have hdescent : baseEnd_1623083 < baseStart_1623083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623117 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1623117 : Nat := 118140960795 + 1623117 * 2 ^ 59
def prefixEnd_1623117 : Nat := 4983230072969 + 3 ^ 40 * 1623117 * 2
def baseEnd_1623117 : Nat := 277813059827943760324309

theorem tailTrace_1623117 : CollatzResearch.WordTrace tailWord_1623117 prefixEnd_1623117 277813059827943760324309 := by
  unfold tailWord_1623117
  simp only [CollatzResearch.WordTrace]
  refine ⟨59199940460731790159187605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39466626973821193439458403 59199940460731790159187605)
  ·
    refine ⟨2774997209096802663711919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59199940460731790159187605 2774997209096802663711919)
    ·
      refine ⟨4162495813645203995567879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774997209096802663711919 4162495813645203995567879)
      ·
        refine ⟨6243743720467805993351819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162495813645203995567879 6243743720467805993351819)
        ·
          refine ⟨9365615580701708990027729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6243743720467805993351819 9365615580701708990027729)
          ·
            refine ⟨7024211685526281742520797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9365615580701708990027729 7024211685526281742520797)
            ·
              refine ⟨2634079382072355653445299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7024211685526281742520797 2634079382072355653445299)
              ·
                refine ⟨3951119073108533480167949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634079382072355653445299 3951119073108533480167949)
                ·
                  refine ⟨1481669652415700055062981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3951119073108533480167949 1481669652415700055062981)
                  ·
                    refine ⟨277813059827943760324309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1481669652415700055062981 277813059827943760324309)
                    ·
                      rfl

theorem cell23_1623117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1623117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623117 prefixEnd_1623117 := by exact prefixLift 1623117
  have htrace : WordTrace (prefixWord ++ tailWord_1623117) baseStart_1623117 baseEnd_1623117 := by
    simpa [prefixWord, tailWord_1623117, baseEnd_1623117] using wordTrace_append hprefix tailTrace_1623117
  have hstable : (prefixWord ++ tailWord_1623117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623117).length < 2 ^ (prefixWord ++ tailWord_1623117).sum := by decide
  have hdescent : baseEnd_1623117 < baseStart_1623117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623140 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_1623140 : Nat := 118140960795 + 1623140 * 2 ^ 59
def prefixEnd_1623140 : Nat := 4983230072969 + 3 ^ 40 * 1623140 * 2
def baseEnd_1623140 : Nat := 833450989538884690985321

theorem tailTrace_1623140 : CollatzResearch.WordTrace tailWord_1623140 prefixEnd_1623140 833450989538884690985321 := by
  unfold tailWord_1623140
  simp only [CollatzResearch.WordTrace]
  refine ⟨29600389669824232543637437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39467186226432310058183249 29600389669824232543637437)
  ·
    refine ⟨11100146126184087203864039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29600389669824232543637437 11100146126184087203864039)
    ·
      refine ⟨16650219189276130805796059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11100146126184087203864039 16650219189276130805796059)
      ·
        refine ⟨24975328783914196208694089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16650219189276130805796059 24975328783914196208694089)
        ·
          refine ⟨18731496587935647156520567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24975328783914196208694089 18731496587935647156520567)
          ·
            refine ⟨28097244881903470734780851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18731496587935647156520567 28097244881903470734780851)
            ·
              refine ⟨42145867322855206102171277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28097244881903470734780851 42145867322855206102171277)
              ·
                refine ⟨15804700246070702288314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42145867322855206102171277 15804700246070702288314229)
                ·
                  refine ⟨1481690648069128339529459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15804700246070702288314229 1481690648069128339529459)
                  ·
                    refine ⟨2222535972103692509294189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1481690648069128339529459 2222535972103692509294189)
                    ·
                      refine ⟨833450989538884690985321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222535972103692509294189 833450989538884690985321)
                      ·
                        rfl

theorem cell23_1623140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_1623140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623140 prefixEnd_1623140 := by exact prefixLift 1623140
  have htrace : WordTrace (prefixWord ++ tailWord_1623140) baseStart_1623140 baseEnd_1623140 := by
    simpa [prefixWord, tailWord_1623140, baseEnd_1623140] using wordTrace_append hprefix tailTrace_1623140
  have hstable : (prefixWord ++ tailWord_1623140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623140).length < 2 ^ (prefixWord ++ tailWord_1623140).sum := by decide
  have hdescent : baseEnd_1623140 < baseStart_1623140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623144 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1623144 : Nat := 118140960795 + 1623144 * 2 ^ 59
def prefixEnd_1623144 : Nat := 4983230072969 + 3 ^ 40 * 1623144 * 2
def baseEnd_1623144 : Nat := 833453043461502675335303

theorem tailTrace_1623144 : CollatzResearch.WordTrace tailWord_1623144 prefixEnd_1623144 833453043461502675335303 := by
  unfold tailWord_1623144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29600462615816986885210243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39467283487755982513613657 29600462615816986885210243)
  ·
    refine ⟨44400693923725480327815365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29600462615816986885210243 44400693923725480327815365)
    ·
      refine ⟨8325130110698527561465381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44400693923725480327815365 8325130110698527561465381)
      ·
        refine ⟨1560961895755973917774759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8325130110698527561465381 1560961895755973917774759)
        ·
          refine ⟨2341442843633960876662139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560961895755973917774759 2341442843633960876662139)
          ·
            refine ⟨3512164265450941314993209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341442843633960876662139 3512164265450941314993209)
            ·
              refine ⟨2634123199088205986244907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512164265450941314993209 2634123199088205986244907)
              ·
                refine ⟨3951184798632308979367361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634123199088205986244907 3951184798632308979367361)
                ·
                  refine ⟨2963388598974231734525521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951184798632308979367361 2963388598974231734525521)
                  ·
                    refine ⟨2222541449230673800894141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963388598974231734525521 2222541449230673800894141)
                    ·
                      refine ⟨833453043461502675335303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222541449230673800894141 833453043461502675335303)
                      ·
                        rfl

theorem cell23_1623144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1623144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623144 prefixEnd_1623144 := by exact prefixLift 1623144
  have htrace : WordTrace (prefixWord ++ tailWord_1623144) baseStart_1623144 baseEnd_1623144 := by
    simpa [prefixWord, tailWord_1623144, baseEnd_1623144] using wordTrace_append hprefix tailTrace_1623144
  have hstable : (prefixWord ++ tailWord_1623144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623144).length < 2 ^ (prefixWord ++ tailWord_1623144).sum := by decide
  have hdescent : baseEnd_1623144 < baseStart_1623144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623200 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1623200 : Nat := 118140960795 + 1623200 * 2 ^ 59
def prefixEnd_1623200 : Nat := 4983230072969 + 3 ^ 40 * 1623200 * 2
def baseEnd_1623200 : Nat := 833481798378154456235045

theorem tailTrace_1623200 : CollatzResearch.WordTrace tailWord_1623200 prefixEnd_1623200 833481798378154456235045 := by
  unfold tailWord_1623200
  simp only [CollatzResearch.WordTrace]
  refine ⟨29601483859715547667229527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39468645146287396889639369 29601483859715547667229527)
  ·
    refine ⟨44402225789573321500844291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29601483859715547667229527 44402225789573321500844291)
    ·
      refine ⟨66603338684359982251266437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44402225789573321500844291 66603338684359982251266437)
      ·
        refine ⟨12488126003317496672112457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66603338684359982251266437 12488126003317496672112457)
        ·
          refine ⟨9366094502488122504084343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12488126003317496672112457 9366094502488122504084343)
          ·
            refine ⟨14049141753732183756126515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9366094502488122504084343 14049141753732183756126515)
            ·
              refine ⟨21073712630598275634189773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14049141753732183756126515 21073712630598275634189773)
              ·
                refine ⟨7902642236474353362821165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21073712630598275634189773 7902642236474353362821165)
                ·
                  refine ⟨2963490838677882511057937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7902642236474353362821165 2963490838677882511057937)
                  ·
                    refine ⟨2222618129008411883293453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963490838677882511057937 2222618129008411883293453)
                    ·
                      refine ⟨833481798378154456235045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222618129008411883293453 833481798378154456235045)
                      ·
                        rfl

theorem cell23_1623200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1623200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623200 prefixEnd_1623200 := by exact prefixLift 1623200
  have htrace : WordTrace (prefixWord ++ tailWord_1623200) baseStart_1623200 baseEnd_1623200 := by
    simpa [prefixWord, tailWord_1623200, baseEnd_1623200] using wordTrace_append hprefix tailTrace_1623200
  have hstable : (prefixWord ++ tailWord_1623200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623200).length < 2 ^ (prefixWord ++ tailWord_1623200).sum := by decide
  have hdescent : baseEnd_1623200 < baseStart_1623200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623263 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 8]
def baseStart_1623263 : Nat := 118140960795 + 1623263 * 2 ^ 59
def prefixEnd_1623263 : Nat := 4983230072969 + 3 ^ 40 * 1623263 * 2
def baseEnd_1623263 : Nat := 277838049219795903249085

theorem tailTrace_1623263 : CollatzResearch.WordTrace tailWord_1623263 prefixEnd_1623263 277838049219795903249085 := by
  unfold tailWord_1623263
  simp only [CollatzResearch.WordTrace]
  refine ⟨59205265518202857094002443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39470177012135238062668295 59205265518202857094002443)
  ·
    refine ⟨88807898277304285641003665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59205265518202857094002443 88807898277304285641003665)
    ·
      refine ⟨66605923707978214230752749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88807898277304285641003665 66605923707978214230752749)
      ·
        refine ⟨24977221390491830336532281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66605923707978214230752749 24977221390491830336532281)
        ·
          refine ⟨18732916042868872752399211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24977221390491830336532281 18732916042868872752399211)
          ·
            refine ⟨28099374064303309128598817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18732916042868872752399211 28099374064303309128598817)
            ·
              refine ⟨21074530548227481846449113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28099374064303309128598817 21074530548227481846449113)
              ·
                refine ⟨15805897911170611384836835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21074530548227481846449113 15805897911170611384836835)
                ·
                  refine ⟨23708846866755917077255253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15805897911170611384836835 23708846866755917077255253)
                  ·
                    refine ⟨277838049219795903249085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23708846866755917077255253 277838049219795903249085)
                    ·
                      rfl

theorem cell23_1623263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_1623263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623263 prefixEnd_1623263 := by exact prefixLift 1623263
  have htrace : WordTrace (prefixWord ++ tailWord_1623263) baseStart_1623263 baseEnd_1623263 := by
    simpa [prefixWord, tailWord_1623263, baseEnd_1623263] using wordTrace_append hprefix tailTrace_1623263
  have hstable : (prefixWord ++ tailWord_1623263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623263).length < 2 ^ (prefixWord ++ tailWord_1623263).sum := by decide
  have hdescent : baseEnd_1623263 < baseStart_1623263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623274 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_1623274 : Nat := 118140960795 + 1623274 * 2 ^ 59
def prefixEnd_1623274 : Nat := 4983230072969 + 3 ^ 40 * 1623274 * 2
def baseEnd_1623274 : Nat := 833519795946587166709705

theorem tailTrace_1623274 : CollatzResearch.WordTrace tailWord_1623274 prefixEnd_1623274 833519795946587166709705 := by
  unfold tailWord_1623274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14801416680290751493163219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39470444480775337315101917 14801416680290751493163219)
  ·
    refine ⟨22202125020436127239744829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14801416680290751493163219 22202125020436127239744829)
    ·
      refine ⟨8325796882663547714904311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22202125020436127239744829 8325796882663547714904311)
      ·
        refine ⟨12488695323995321572356467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8325796882663547714904311 12488695323995321572356467)
        ·
          refine ⟨18733042985992982358534701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488695323995321572356467 18733042985992982358534701)
          ·
            refine ⟨7024891119747368384450513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18733042985992982358534701 7024891119747368384450513)
            ·
              refine ⟨5268668339810526288337885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7024891119747368384450513 5268668339810526288337885)
              ·
                refine ⟨1975750627428947358126707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5268668339810526288337885 1975750627428947358126707)
                ·
                  refine ⟨2963625941143421037190061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975750627428947358126707 2963625941143421037190061)
                  ·
                    refine ⟨1111359727928782888946273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963625941143421037190061 1111359727928782888946273)
                    ·
                      refine ⟨833519795946587166709705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111359727928782888946273 833519795946587166709705)
                      ·
                        rfl

theorem cell23_1623274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_1623274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623274 prefixEnd_1623274 := by exact prefixLift 1623274
  have htrace : WordTrace (prefixWord ++ tailWord_1623274) baseStart_1623274 baseEnd_1623274 := by
    simpa [prefixWord, tailWord_1623274, baseEnd_1623274] using wordTrace_append hprefix tailTrace_1623274
  have hstable : (prefixWord ++ tailWord_1623274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623274).length < 2 ^ (prefixWord ++ tailWord_1623274).sum := by decide
  have hdescent : baseEnd_1623274 < baseStart_1623274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623290 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_1623290 : Nat := 118140960795 + 1623290 * 2 ^ 59
def prefixEnd_1623290 : Nat := 4983230072969 + 3 ^ 40 * 1623290 * 2
def baseEnd_1623290 : Nat := 833528011637059104109631

theorem tailTrace_1623290 : CollatzResearch.WordTrace tailWord_1623290 prefixEnd_1623290 833528011637059104109631 := by
  unfold tailWord_1623290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14801562572276260176308831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39470833526070027136823549 14801562572276260176308831)
  ·
    refine ⟨22202343858414390264463247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14801562572276260176308831 22202343858414390264463247)
    ·
      refine ⟨33303515787621585396694871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22202343858414390264463247 33303515787621585396694871)
      ·
        refine ⟨49955273681432378095042307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33303515787621585396694871 49955273681432378095042307)
        ·
          refine ⟨74932910522148567142563461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49955273681432378095042307 74932910522148567142563461)
          ·
            refine ⟨14049920722902856339230649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74932910522148567142563461 14049920722902856339230649)
            ·
              refine ⟨10537440542177142254422987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14049920722902856339230649 10537440542177142254422987)
              ·
                refine ⟨15806160813265713381634481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10537440542177142254422987 15806160813265713381634481)
                ·
                  refine ⟨11854620609949285036225861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15806160813265713381634481 11854620609949285036225861)
                  ·
                    refine ⟨2222741364365490944292349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11854620609949285036225861 2222741364365490944292349)
                    ·
                      refine ⟨833528011637059104109631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222741364365490944292349 833528011637059104109631)
                      ·
                        rfl

theorem cell23_1623290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_1623290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623290 prefixEnd_1623290 := by exact prefixLift 1623290
  have htrace : WordTrace (prefixWord ++ tailWord_1623290) baseStart_1623290 baseEnd_1623290 := by
    simpa [prefixWord, tailWord_1623290, baseEnd_1623290] using wordTrace_append hprefix tailTrace_1623290
  have hstable : (prefixWord ++ tailWord_1623290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623290).length < 2 ^ (prefixWord ++ tailWord_1623290).sum := by decide
  have hdescent : baseEnd_1623290 < baseStart_1623290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623338 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1623338 : Nat := 118140960795 + 1623338 * 2 ^ 59
def prefixEnd_1623338 : Nat := 4983230072969 + 3 ^ 40 * 1623338 * 2
def baseEnd_1623338 : Nat := 833552658708474916309411

theorem tailTrace_1623338 : CollatzResearch.WordTrace tailWord_1623338 prefixEnd_1623338 833552658708474916309411 := by
  unfold tailWord_1623338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14802000248232786225745667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39472000661954096601988445 14802000248232786225745667)
  ·
    refine ⟨22203000372349179338618501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14802000248232786225745667 22203000372349179338618501)
    ·
      refine ⟨4163062569815471125990969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22203000372349179338618501 4163062569815471125990969)
      ·
        refine ⟨3122296927361603344493227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4163062569815471125990969 3122296927361603344493227)
        ·
          refine ⟨4683445391042405016739841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122296927361603344493227 4683445391042405016739841)
          ·
            refine ⟨3512584043281803762554881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683445391042405016739841 3512584043281803762554881)
            ·
              refine ⟨2634438032461352821916161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512584043281803762554881 2634438032461352821916161)
              ·
                refine ⟨1975828524346014616437121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634438032461352821916161 1975828524346014616437121)
                ·
                  refine ⟨1481871393259510962327841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1975828524346014616437121 1481871393259510962327841)
                  ·
                    refine ⟨1111403544944633221745881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1481871393259510962327841 1111403544944633221745881)
                    ·
                      refine ⟨833552658708474916309411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111403544944633221745881 833552658708474916309411)
                      ·
                        rfl

theorem cell23_1623338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1623338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623338 prefixEnd_1623338 := by exact prefixLift 1623338
  have htrace : WordTrace (prefixWord ++ tailWord_1623338) baseStart_1623338 baseEnd_1623338 := by
    simpa [prefixWord, tailWord_1623338, baseEnd_1623338] using wordTrace_append hprefix tailTrace_1623338
  have hstable : (prefixWord ++ tailWord_1623338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623338).length < 2 ^ (prefixWord ++ tailWord_1623338).sum := by decide
  have hdescent : baseEnd_1623338 < baseStart_1623338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623347 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 2, 5, 2]
def baseStart_1623347 : Nat := 118140960795 + 1623347 * 2 ^ 59
def prefixEnd_1623347 : Nat := 4983230072969 + 3 ^ 40 * 1623347 * 2
def baseEnd_1623347 : Nat := 833557280034365381096869

theorem tailTrace_1623347 : CollatzResearch.WordTrace tailWord_1623347 prefixEnd_1623347 833557280034365381096869 := by
  unfold tailWord_1623347
  simp only [CollatzResearch.WordTrace]
  refine ⟨59208329249898539440060295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39472219499932359626706863 59208329249898539440060295)
  ·
    refine ⟨88812493874847809160090443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59208329249898539440060295 88812493874847809160090443)
    ·
      refine ⟨133218740812271713740135665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88812493874847809160090443 133218740812271713740135665)
      ·
        refine ⟨99914055609203785305101749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133218740812271713740135665 99914055609203785305101749)
        ·
          refine ⟨9366942713362854872353289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99914055609203785305101749 9366942713362854872353289)
          ·
            refine ⟨7025207035022141154264967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9366942713362854872353289 7025207035022141154264967)
            ·
              refine ⟨10537810552533211731397451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025207035022141154264967 10537810552533211731397451)
              ·
                refine ⟨15806715828799817597096177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10537810552533211731397451 15806715828799817597096177)
                ·
                  refine ⟨11855036871599863197822133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15806715828799817597096177 11855036871599863197822133)
                  ·
                    refine ⟨1111409706712487174795825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11855036871599863197822133 1111409706712487174795825)
                    ·
                      refine ⟨833557280034365381096869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111409706712487174795825 833557280034365381096869)
                      ·
                        rfl

theorem cell23_1623347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 5, 2].length) (baseStart_1623347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623347 prefixEnd_1623347 := by exact prefixLift 1623347
  have htrace : WordTrace (prefixWord ++ tailWord_1623347) baseStart_1623347 baseEnd_1623347 := by
    simpa [prefixWord, tailWord_1623347, baseEnd_1623347] using wordTrace_append hprefix tailTrace_1623347
  have hstable : (prefixWord ++ tailWord_1623347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623347).length < 2 ^ (prefixWord ++ tailWord_1623347).sum := by decide
  have hdescent : baseEnd_1623347 < baseStart_1623347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623360 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_1623360 : Nat := 118140960795 + 1623360 * 2 ^ 59
def prefixEnd_1623360 : Nat := 4983230072969 + 3 ^ 40 * 1623360 * 2
def baseEnd_1623360 : Nat := 833563955282873830234309

theorem tailTrace_1623360 : CollatzResearch.WordTrace tailWord_1623360 prefixEnd_1623360 833563955282873830234309 := by
  unfold tailWord_1623360
  simp only [CollatzResearch.WordTrace]
  refine ⟨29604401699425721330141767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39472535599234295106855689 29604401699425721330141767)
  ·
    refine ⟨44406602549138581995212651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29604401699425721330141767 44406602549138581995212651)
    ·
      refine ⟨66609903823707872992818977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44406602549138581995212651 66609903823707872992818977)
      ·
        refine ⟨49957427867780904744614233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66609903823707872992818977 49957427867780904744614233)
        ·
          refine ⟨37468070900835678558460675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49957427867780904744614233 37468070900835678558460675)
          ·
            refine ⟨56202106351253517837691013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37468070900835678558460675 56202106351253517837691013)
            ·
              refine ⟨10537894940860034594567065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56202106351253517837691013 10537894940860034594567065)
              ·
                refine ⟨7903421205645025945925299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10537894940860034594567065 7903421205645025945925299)
                ·
                  refine ⟨11855131808467538918887949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903421205645025945925299 11855131808467538918887949)
                  ·
                    refine ⟨4445674428175327094582981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11855131808467538918887949 4445674428175327094582981)
                    ·
                      refine ⟨833563955282873830234309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4445674428175327094582981 833563955282873830234309)
                      ·
                        rfl

theorem cell23_1623360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_1623360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623360 prefixEnd_1623360 := by exact prefixLift 1623360
  have htrace : WordTrace (prefixWord ++ tailWord_1623360) baseStart_1623360 baseEnd_1623360 := by
    simpa [prefixWord, tailWord_1623360, baseEnd_1623360] using wordTrace_append hprefix tailTrace_1623360
  have hstable : (prefixWord ++ tailWord_1623360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623360).length < 2 ^ (prefixWord ++ tailWord_1623360).sum := by decide
  have hdescent : baseEnd_1623360 < baseStart_1623360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623377 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 1, 6, 2]
def baseStart_1623377 : Nat := 118140960795 + 1623377 * 2 ^ 59
def prefixEnd_1623377 : Nat := 4983230072969 + 3 ^ 40 * 1623377 * 2
def baseEnd_1623377 : Nat := 833572684454000263721731

theorem tailTrace_1623377 : CollatzResearch.WordTrace tailWord_1623377 prefixEnd_1623377 833572684454000263721731 := by
  unfold tailWord_1623377
  simp only [CollatzResearch.WordTrace]
  refine ⟨59209423439789854563652385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39472948959859903042434923 59209423439789854563652385)
  ·
    refine ⟨44407067579842390922739289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59209423439789854563652385 44407067579842390922739289)
    ·
      refine ⟨33305300684881793192054467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44407067579842390922739289 33305300684881793192054467)
      ·
        refine ⟨49957951027322689788081701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33305300684881793192054467 49957951027322689788081701)
        ·
          refine ⟨9367115817623004335265319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49957951027322689788081701 9367115817623004335265319)
          ·
            refine ⟨14050673726434506502897979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9367115817623004335265319 14050673726434506502897979)
            ·
              refine ⟨21076010589651759754346969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14050673726434506502897979 21076010589651759754346969)
              ·
                refine ⟨15807007942238819815760227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21076010589651759754346969 15807007942238819815760227)
                ·
                  refine ⟨23710511913358229723640341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15807007942238819815760227 23710511913358229723640341)
                  ·
                    refine ⟨1111430245938667018295641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23710511913358229723640341 1111430245938667018295641)
                    ·
                      refine ⟨833572684454000263721731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111430245938667018295641 833572684454000263721731)
                      ·
                        rfl

theorem cell23_1623377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_1623377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623377 prefixEnd_1623377 := by exact prefixLift 1623377
  have htrace : WordTrace (prefixWord ++ tailWord_1623377) baseStart_1623377 baseEnd_1623377 := by
    simpa [prefixWord, tailWord_1623377, baseEnd_1623377] using wordTrace_append hprefix tailTrace_1623377
  have hstable : (prefixWord ++ tailWord_1623377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623377).length < 2 ^ (prefixWord ++ tailWord_1623377).sum := by decide
  have hdescent : baseEnd_1623377 < baseStart_1623377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623389 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1623389 : Nat := 118140960795 + 1623389 * 2 ^ 59
def prefixEnd_1623389 : Nat := 4983230072969 + 3 ^ 40 * 1623389 * 2
def baseEnd_1623389 : Nat := 833578846221854216771677

theorem tailTrace_1623389 : CollatzResearch.WordTrace tailWord_1623389 prefixEnd_1623389 833578846221854216771677 := by
  unfold tailWord_1623389
  simp only [CollatzResearch.WordTrace]
  refine ⟨59209861115746380613089221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39473240743830920408726147 59209861115746380613089221)
  ·
    refine ⟨11101848959202446364954229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59209861115746380613089221 11101848959202446364954229)
    ·
      refine ⟨1040798339925229346714459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11101848959202446364954229 1040798339925229346714459)
      ·
        refine ⟨1561197509887844020071689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040798339925229346714459 1561197509887844020071689)
        ·
          refine ⟨1170898132415883015053767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1561197509887844020071689 1170898132415883015053767)
          ·
            refine ⟨1756347198623824522580651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170898132415883015053767 1756347198623824522580651)
            ·
              refine ⟨2634520797935736783870977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756347198623824522580651 2634520797935736783870977)
              ·
                refine ⟨1975890598451802587903233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634520797935736783870977 1975890598451802587903233)
                ·
                  refine ⟨1481917948838851940927425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1975890598451802587903233 1481917948838851940927425)
                  ·
                    refine ⟨1111438461629138955695569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1481917948838851940927425 1111438461629138955695569)
                    ·
                      refine ⟨833578846221854216771677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111438461629138955695569 833578846221854216771677)
                      ·
                        rfl

theorem cell23_1623389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1623389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623389 prefixEnd_1623389 := by exact prefixLift 1623389
  have htrace : WordTrace (prefixWord ++ tailWord_1623389) baseStart_1623389 baseEnd_1623389 := by
    simpa [prefixWord, tailWord_1623389, baseEnd_1623389] using wordTrace_append hprefix tailTrace_1623389
  have hstable : (prefixWord ++ tailWord_1623389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623389).length < 2 ^ (prefixWord ++ tailWord_1623389).sum := by decide
  have hdescent : baseEnd_1623389 < baseStart_1623389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623394 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1623394 : Nat := 118140960795 + 1623394 * 2 ^ 59
def prefixEnd_1623394 : Nat := 4983230072969 + 3 ^ 40 * 1623394 * 2
def baseEnd_1623394 : Nat := 833581413625126697209153

theorem tailTrace_1623394 : CollatzResearch.WordTrace tailWord_1623394 prefixEnd_1623394 833581413625126697209153 := by
  unfold tailWord_1623394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14802510870182066616755309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39473362320485510978014157 14802510870182066616755309)
  ·
    refine ⟨5550941576318274981283241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14802510870182066616755309 5550941576318274981283241)
    ·
      refine ⟨4163206182238706235962431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5550941576318274981283241 4163206182238706235962431)
      ·
        refine ⟨6244809273358059353943647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163206182238706235962431 6244809273358059353943647)
        ·
          refine ⟨9367213910037089030915471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6244809273358059353943647 9367213910037089030915471)
          ·
            refine ⟨14050820865055633546373207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9367213910037089030915471 14050820865055633546373207)
            ·
              refine ⟨21076231297583450319559811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14050820865055633546373207 21076231297583450319559811)
              ·
                refine ⟨31614346946375175479339717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21076231297583450319559811 31614346946375175479339717)
                ·
                  refine ⟨5927690052445345402376197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31614346946375175479339717 5927690052445345402376197)
                  ·
                    refine ⟨1111441884833502262945537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927690052445345402376197 1111441884833502262945537)
                    ·
                      refine ⟨833581413625126697209153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111441884833502262945537 833581413625126697209153)
                      ·
                        rfl

theorem cell23_1623394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1623394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623394 prefixEnd_1623394 := by exact prefixLift 1623394
  have htrace : WordTrace (prefixWord ++ tailWord_1623394) baseStart_1623394 baseEnd_1623394 := by
    simpa [prefixWord, tailWord_1623394, baseEnd_1623394] using wordTrace_append hprefix tailTrace_1623394
  have hstable : (prefixWord ++ tailWord_1623394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623394).length < 2 ^ (prefixWord ++ tailWord_1623394).sum := by decide
  have hdescent : baseEnd_1623394 < baseStart_1623394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623397 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1623397 : Nat := 118140960795 + 1623397 * 2 ^ 59
def prefixEnd_1623397 : Nat := 4983230072969 + 3 ^ 40 * 1623397 * 2
def baseEnd_1623397 : Nat := 833582954067090185471639

theorem tailTrace_1623397 : CollatzResearch.WordTrace tailWord_1623397 prefixEnd_1623397 833582954067090185471639 := by
  unfold tailWord_1623397
  simp only [CollatzResearch.WordTrace]
  refine ⟨59210152899717397979380445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39473435266478265319586963 59210152899717397979380445)
  ·
    refine ⟨22203807337394024242267667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59210152899717397979380445 22203807337394024242267667)
    ·
      refine ⟨33305711006091036363401501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22203807337394024242267667 33305711006091036363401501)
      ·
        refine ⟨12489641627284138636275563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33305711006091036363401501 12489641627284138636275563)
        ·
          refine ⟨18734462440926207954413345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12489641627284138636275563 18734462440926207954413345)
          ·
            refine ⟨14050846830694655965810009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18734462440926207954413345 14050846830694655965810009)
            ·
              refine ⟨10538135123020991974357507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14050846830694655965810009 10538135123020991974357507)
              ·
                refine ⟨15807202684531487961536261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538135123020991974357507 15807202684531487961536261)
                ·
                  refine ⟨2963850503349653992788049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15807202684531487961536261 2963850503349653992788049)
                  ·
                    refine ⟨2222887877512240494591037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963850503349653992788049 2222887877512240494591037)
                    ·
                      refine ⟨833582954067090185471639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2222887877512240494591037 833582954067090185471639)
                      ·
                        rfl

theorem cell23_1623397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1623397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623397 prefixEnd_1623397 := by exact prefixLift 1623397
  have htrace : WordTrace (prefixWord ++ tailWord_1623397) baseStart_1623397 baseEnd_1623397 := by
    simpa [prefixWord, tailWord_1623397, baseEnd_1623397] using wordTrace_append hprefix tailTrace_1623397
  have hstable : (prefixWord ++ tailWord_1623397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623397).length < 2 ^ (prefixWord ++ tailWord_1623397).sum := by decide
  have hdescent : baseEnd_1623397 < baseStart_1623397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623404 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_1623404 : Nat := 118140960795 + 1623404 * 2 ^ 59
def prefixEnd_1623404 : Nat := 4983230072969 + 3 ^ 40 * 1623404 * 2
def baseEnd_1623404 : Nat := 277862182810557219361369

theorem tailTrace_1623404 : CollatzResearch.WordTrace tailWord_1623404 prefixEnd_1623404 277862182810557219361369 := by
  unfold tailWord_1623404
  simp only [CollatzResearch.WordTrace]
  refine ⟨29605204105346019087442633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39473605473794692116590177 29605204105346019087442633)
  ·
    refine ⟨22203903079009514315581975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29605204105346019087442633 22203903079009514315581975)
    ·
      refine ⟨33305854618514271473372963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22203903079009514315581975 33305854618514271473372963)
      ·
        refine ⟨49958781927771407210059445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33305854618514271473372963 49958781927771407210059445)
        ·
          refine ⟨4683635805728569425943073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49958781927771407210059445 4683635805728569425943073)
          ·
            refine ⟨3512726854296427069457305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683635805728569425943073 3512726854296427069457305)
            ·
              refine ⟨2634545140722320302092979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512726854296427069457305 2634545140722320302092979)
              ·
                refine ⟨3951817711083480453139469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634545140722320302092979 3951817711083480453139469)
                ·
                  refine ⟨1481931641656305169927301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3951817711083480453139469 1481931641656305169927301)
                  ·
                    refine ⟨277862182810557219361369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1481931641656305169927301 277862182810557219361369)
                    ·
                      rfl

theorem cell23_1623404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_1623404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623404 prefixEnd_1623404 := by exact prefixLift 1623404
  have htrace : WordTrace (prefixWord ++ tailWord_1623404) baseStart_1623404 baseEnd_1623404 := by
    simpa [prefixWord, tailWord_1623404, baseEnd_1623404] using wordTrace_append hprefix tailTrace_1623404
  have hstable : (prefixWord ++ tailWord_1623404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623404).length < 2 ^ (prefixWord ++ tailWord_1623404).sum := by decide
  have hdescent : baseEnd_1623404 < baseStart_1623404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623420 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1623420 : Nat := 118140960795 + 1623420 * 2 ^ 59
def prefixEnd_1623420 : Nat := 4983230072969 + 3 ^ 40 * 1623420 * 2
def baseEnd_1623420 : Nat := 833594764122143595484033

theorem tailTrace_1623420 : CollatzResearch.WordTrace tailWord_1623420 prefixEnd_1623420 833594764122143595484033 := by
  unfold tailWord_1623420
  simp only [CollatzResearch.WordTrace]
  refine ⟨29605495889317036453733857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39473994519089381938311809 29605495889317036453733857)
  ·
    refine ⟨22204121916987777340300393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29605495889317036453733857 22204121916987777340300393)
    ·
      refine ⟨16653091437740833005225295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22204121916987777340300393 16653091437740833005225295)
      ·
        refine ⟨24979637156611249507837943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16653091437740833005225295 24979637156611249507837943)
        ·
          refine ⟨37469455734916874261756915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24979637156611249507837943 37469455734916874261756915)
          ·
            refine ⟨56204183602375311392635373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37469455734916874261756915 56204183602375311392635373)
            ·
              refine ⟨21076568850890741772238265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56204183602375311392635373 21076568850890741772238265)
              ·
                refine ⟨15807426638168056329178699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21076568850890741772238265 15807426638168056329178699)
                ·
                  refine ⟨23711139957252084493768049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15807426638168056329178699 23711139957252084493768049)
                  ·
                    refine ⟨17783354967939063370326037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23711139957252084493768049 17783354967939063370326037)
                    ·
                      refine ⟨833594764122143595484033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17783354967939063370326037 833594764122143595484033)
                      ·
                        rfl

theorem cell23_1623420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1623420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623420 prefixEnd_1623420 := by exact prefixLift 1623420
  have htrace : WordTrace (prefixWord ++ tailWord_1623420) baseStart_1623420 baseEnd_1623420 := by
    simpa [prefixWord, tailWord_1623420, baseEnd_1623420] using wordTrace_append hprefix tailTrace_1623420
  have hstable : (prefixWord ++ tailWord_1623420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623420).length < 2 ^ (prefixWord ++ tailWord_1623420).sum := by decide
  have hdescent : baseEnd_1623420 < baseStart_1623420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623467 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 3, 8, 2]
def baseStart_1623467 : Nat := 118140960795 + 1623467 * 2 ^ 59
def prefixEnd_1623467 : Nat := 4983230072969 + 3 ^ 40 * 1623467 * 2
def baseEnd_1623467 : Nat := 833618897712904911596317

theorem tailTrace_1623467 : CollatzResearch.WordTrace tailWord_1623467 prefixEnd_1623467 833618897712904911596317 := by
  unfold tailWord_1623467
  simp only [CollatzResearch.WordTrace]
  refine ⟨59212706009463799934428655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39475137339642533289619103 59212706009463799934428655)
  ·
    refine ⟨88819059014195699901642983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59212706009463799934428655 88819059014195699901642983)
    ·
      refine ⟨133228588521293549852464475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88819059014195699901642983 133228588521293549852464475)
      ·
        refine ⟨199842882781940324778696713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133228588521293549852464475 199842882781940324778696713)
        ·
          refine ⟨149882162086455243584022535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199842882781940324778696713 149882162086455243584022535)
          ·
            refine ⟨224823243129682865376033803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149882162086455243584022535 224823243129682865376033803)
            ·
              refine ⟨337234864694524298064050705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224823243129682865376033803 337234864694524298064050705)
              ·
                refine ⟨252926148520893223548038029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337234864694524298064050705 252926148520893223548038029)
                ·
                  refine ⟨94847305695334958830514261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252926148520893223548038029 94847305695334958830514261)
                  ·
                    refine ⟨1111491863617206548795089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94847305695334958830514261 1111491863617206548795089)
                    ·
                      refine ⟨833618897712904911596317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111491863617206548795089 833618897712904911596317)
                      ·
                        rfl

theorem cell23_1623467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 8, 2].length) (baseStart_1623467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623467 prefixEnd_1623467 := by exact prefixLift 1623467
  have htrace : WordTrace (prefixWord ++ tailWord_1623467) baseStart_1623467 baseEnd_1623467 := by
    simpa [prefixWord, tailWord_1623467, baseEnd_1623467] using wordTrace_append hprefix tailTrace_1623467
  have hstable : (prefixWord ++ tailWord_1623467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623467).length < 2 ^ (prefixWord ++ tailWord_1623467).sum := by decide
  have hdescent : baseEnd_1623467 < baseStart_1623467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623481 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 1, 5]
def baseStart_1623481 : Nat := 118140960795 + 1623481 * 2 ^ 59
def prefixEnd_1623481 : Nat := 4983230072969 + 3 ^ 40 * 1623481 * 2
def baseEnd_1623481 : Nat := 277875362147355952273751

theorem tailTrace_1623481 : CollatzResearch.WordTrace tailWord_1623481 prefixEnd_1623481 277875362147355952273751 := by
  unfold tailWord_1623481
  simp only [CollatzResearch.WordTrace]
  refine ⟨59213216631413080325438297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39475477754275386883625531 59213216631413080325438297)
  ·
    refine ⟨44409912473559810244078723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59213216631413080325438297 44409912473559810244078723)
    ·
      refine ⟨66614868710339715366118085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44409912473559810244078723 66614868710339715366118085)
      ·
        refine ⟨12490287883188696631147141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66614868710339715366118085 12490287883188696631147141)
        ·
          refine ⟨2341928978097880618340089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12490287883188696631147141 2341928978097880618340089)
          ·
            refine ⟨1756446733573410463755067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2341928978097880618340089 1756446733573410463755067)
            ·
              refine ⟨2634670100360115695632601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756446733573410463755067 2634670100360115695632601)
              ·
                refine ⟨1976002575270086771724451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634670100360115695632601 1976002575270086771724451)
                ·
                  refine ⟨2964003862905130157586677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976002575270086771724451 2964003862905130157586677)
                  ·
                    refine ⟨277875362147355952273751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2964003862905130157586677 277875362147355952273751)
                    ·
                      rfl

theorem cell23_1623481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 5].length) (baseStart_1623481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623481 prefixEnd_1623481 := by exact prefixLift 1623481
  have htrace : WordTrace (prefixWord ++ tailWord_1623481) baseStart_1623481 baseEnd_1623481 := by
    simpa [prefixWord, tailWord_1623481, baseEnd_1623481] using wordTrace_append hprefix tailTrace_1623481
  have hstable : (prefixWord ++ tailWord_1623481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623481).length < 2 ^ (prefixWord ++ tailWord_1623481).sum := by decide
  have hdescent : baseEnd_1623481 < baseStart_1623481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623541 : List Nat := [1, 3, 5, 1, 1, 2, 3, 7]
def baseStart_1623541 : Nat := 118140960795 + 1623541 * 2 ^ 59
def prefixEnd_1623541 : Nat := 4983230072969 + 3 ^ 40 * 1623541 * 2
def baseEnd_1623541 : Nat := 30876181306716208224851

theorem tailTrace_1623541 : CollatzResearch.WordTrace tailWord_1623541 prefixEnd_1623541 30876181306716208224851 := by
  unfold tailWord_1623541
  simp only [CollatzResearch.WordTrace]
  refine ⟨59215405011195710572622477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39476936674130473715081651 59215405011195710572622477)
  ·
    refine ⟨22205776879198391464733429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59215405011195710572622477 22205776879198391464733429)
    ·
      refine ⟨2081791582424849199818759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22205776879198391464733429 2081791582424849199818759)
      ·
        refine ⟨3122687373637273799728139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081791582424849199818759 3122687373637273799728139)
        ·
          refine ⟨4684031060455910699592209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122687373637273799728139 4684031060455910699592209)
          ·
            refine ⟨3513023295341933024694157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4684031060455910699592209 3513023295341933024694157)
            ·
              refine ⟨1317383735753224884260309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3513023295341933024694157 1317383735753224884260309)
              ·
                refine ⟨30876181306716208224851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1317383735753224884260309 30876181306716208224851)
                ·
                  rfl

theorem cell23_1623541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 7].length) (baseStart_1623541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623541 prefixEnd_1623541 := by exact prefixLift 1623541
  have htrace : WordTrace (prefixWord ++ tailWord_1623541) baseStart_1623541 baseEnd_1623541 := by
    simpa [prefixWord, tailWord_1623541, baseEnd_1623541] using wordTrace_append hprefix tailTrace_1623541
  have hstable : (prefixWord ++ tailWord_1623541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623541).length < 2 ^ (prefixWord ++ tailWord_1623541).sum := by decide
  have hdescent : baseEnd_1623541 < baseStart_1623541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623558 : List Nat := [6, 2, 1, 1, 2, 1, 10]
def baseStart_1623558 : Nat := 118140960795 + 1623558 * 2 ^ 59
def prefixEnd_1623558 : Nat := 4983230072969 + 3 ^ 40 * 1623558 * 2
def baseEnd_1623558 : Nat := 10292168203116840192079

theorem tailTrace_1623558 : CollatzResearch.WordTrace tailWord_1623558 prefixEnd_1623558 10292168203116840192079 := by
  unfold tailWord_1623558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850500782879191327374729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39477350034756081650660885 1850500782879191327374729)
  ·
    refine ⟨1387875587159393495531047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1850500782879191327374729 1387875587159393495531047)
    ·
      refine ⟨2081813380739090243296571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387875587159393495531047 2081813380739090243296571)
      ·
        refine ⟨3122720071108635364944857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081813380739090243296571 3122720071108635364944857)
        ·
          refine ⟨2342040053331476523708643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122720071108635364944857 2342040053331476523708643)
          ·
            refine ⟨3513060079997214785562965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342040053331476523708643 3513060079997214785562965)
            ·
              refine ⟨10292168203116840192079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3513060079997214785562965 10292168203116840192079)
              ·
                rfl

theorem cell23_1623558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 10].length) (baseStart_1623558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623558 prefixEnd_1623558 := by exact prefixLift 1623558
  have htrace : WordTrace (prefixWord ++ tailWord_1623558) baseStart_1623558 baseEnd_1623558 := by
    simpa [prefixWord, tailWord_1623558, baseEnd_1623558] using wordTrace_append hprefix tailTrace_1623558
  have hstable : (prefixWord ++ tailWord_1623558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623558).length < 2 ^ (prefixWord ++ tailWord_1623558).sum := by decide
  have hdescent : baseEnd_1623558 < baseStart_1623558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623561 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 1, 3, 2]
def baseStart_1623561 : Nat := 118140960795 + 1623561 * 2 ^ 59
def prefixEnd_1623561 : Nat := 4983230072969 + 3 ^ 40 * 1623561 * 2
def baseEnd_1623561 : Nat := 833667164894427543820885

theorem tailTrace_1623561 : CollatzResearch.WordTrace tailWord_1623561 prefixEnd_1623561 833667164894427543820885 := by
  unfold tailWord_1623561
  simp only [CollatzResearch.WordTrace]
  refine ⟨59216134471123253988350537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39477422980748835992233691 59216134471123253988350537)
  ·
    refine ⟨44412100853342440491262903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59216134471123253988350537 44412100853342440491262903)
    ·
      refine ⟨66618151280013660736894355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44412100853342440491262903 66618151280013660736894355)
      ·
        refine ⟨99927226920020491105341533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66618151280013660736894355 99927226920020491105341533)
        ·
          refine ⟨37472710095007684164503075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99927226920020491105341533 37472710095007684164503075)
          ·
            refine ⟨56209065142511526246754613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37472710095007684164503075 56209065142511526246754613)
            ·
              refine ⟨5269599857110455585633245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56209065142511526246754613 5269599857110455585633245)
              ·
                refine ⟨1976099946416420844612467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5269599857110455585633245 1976099946416420844612467)
                ·
                  refine ⟨2964149919624631266918701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976099946416420844612467 2964149919624631266918701)
                  ·
                    refine ⟨1111556219859236725094513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2964149919624631266918701 1111556219859236725094513)
                    ·
                      refine ⟨833667164894427543820885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111556219859236725094513 833667164894427543820885)
                      ·
                        rfl

theorem cell23_1623561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 3, 2].length) (baseStart_1623561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623561 prefixEnd_1623561 := by exact prefixLift 1623561
  have htrace : WordTrace (prefixWord ++ tailWord_1623561) baseStart_1623561 baseEnd_1623561 := by
    simpa [prefixWord, tailWord_1623561, baseEnd_1623561] using wordTrace_append hprefix tailTrace_1623561
  have hstable : (prefixWord ++ tailWord_1623561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623561).length < 2 ^ (prefixWord ++ tailWord_1623561).sum := by decide
  have hdescent : baseEnd_1623561 < baseStart_1623561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623582 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1623582 : Nat := 118140960795 + 1623582 * 2 ^ 59
def prefixEnd_1623582 : Nat := 4983230072969 + 3 ^ 40 * 1623582 * 2
def baseEnd_1623582 : Nat := 833677947988171961658289

theorem tailTrace_1623582 : CollatzResearch.WordTrace tailWord_1623582 prefixEnd_1623582 833677947988171961658289 := by
  unfold tailWord_1623582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402112550505896821858125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39477933602698116383243333 7402112550505896821858125)
  ·
    refine ⟨2775792206439711308196797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7402112550505896821858125 2775792206439711308196797)
    ·
      refine ⟨1040922077414891740573799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2775792206439711308196797 1040922077414891740573799)
      ·
        refine ⟨1561383116122337610860699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040922077414891740573799 1561383116122337610860699)
        ·
          refine ⟨2342074674183506416291049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561383116122337610860699 2342074674183506416291049)
          ·
            refine ⟨1756556005637629812218287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342074674183506416291049 1756556005637629812218287)
            ·
              refine ⟨2634834008456444718327431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756556005637629812218287 2634834008456444718327431)
              ·
                refine ⟨3952251012684667077491147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634834008456444718327431 3952251012684667077491147)
                ·
                  refine ⟨5928376519027000616236721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952251012684667077491147 5928376519027000616236721)
                  ·
                    refine ⟨4446282389270250462177541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5928376519027000616236721 4446282389270250462177541)
                    ·
                      refine ⟨833677947988171961658289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4446282389270250462177541 833677947988171961658289)
                      ·
                        rfl

theorem cell23_1623582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1623582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623582 prefixEnd_1623582 := by exact prefixLift 1623582
  have htrace : WordTrace (prefixWord ++ tailWord_1623582) baseStart_1623582 baseEnd_1623582 := by
    simpa [prefixWord, tailWord_1623582, baseEnd_1623582] using wordTrace_append hprefix tailTrace_1623582
  have hstable : (prefixWord ++ tailWord_1623582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623582).length < 2 ^ (prefixWord ++ tailWord_1623582).sum := by decide
  have hdescent : baseEnd_1623582 < baseStart_1623582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623584 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_1623584 : Nat := 118140960795 + 1623584 * 2 ^ 59
def prefixEnd_1623584 : Nat := 4983230072969 + 3 ^ 40 * 1623584 * 2
def baseEnd_1623584 : Nat := 277892991649826984611093

theorem tailTrace_1623584 : CollatzResearch.WordTrace tailWord_1623584 prefixEnd_1623584 277892991649826984611093 := by
  unfold tailWord_1623584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29608486675019964458218903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39477982233359952610958537 29608486675019964458218903)
  ·
    refine ⟨44412730012529946687328355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29608486675019964458218903 44412730012529946687328355)
    ·
      refine ⟨66619095018794920030992533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44412730012529946687328355 66619095018794920030992533)
      ·
        refine ⟨3122770079006011876452775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66619095018794920030992533 3122770079006011876452775)
        ·
          refine ⟨4684155118509017814679163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122770079006011876452775 4684155118509017814679163)
          ·
            refine ⟨7026232677763526722018745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4684155118509017814679163 7026232677763526722018745)
            ·
              refine ⟨5269674508322645041514059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026232677763526722018745 5269674508322645041514059)
              ·
                refine ⟨7904511762483967562271089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269674508322645041514059 7904511762483967562271089)
                ·
                  refine ⟨5928383821862975671703317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904511762483967562271089 5928383821862975671703317)
                  ·
                    refine ⟨277892991649826984611093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5928383821862975671703317 277892991649826984611093)
                    ·
                      rfl

theorem cell23_1623584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_1623584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623584 prefixEnd_1623584 := by exact prefixLift 1623584
  have htrace : WordTrace (prefixWord ++ tailWord_1623584) baseStart_1623584 baseEnd_1623584 := by
    simpa [prefixWord, tailWord_1623584, baseEnd_1623584] using wordTrace_append hprefix tailTrace_1623584
  have hstable : (prefixWord ++ tailWord_1623584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623584).length < 2 ^ (prefixWord ++ tailWord_1623584).sum := by decide
  have hdescent : baseEnd_1623584 < baseStart_1623584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623594 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1623594 : Nat := 118140960795 + 1623594 * 2 ^ 59
def prefixEnd_1623594 : Nat := 4983230072969 + 3 ^ 40 * 1623594 * 2
def baseEnd_1623594 : Nat := 833684109756025914708233

theorem tailTrace_1623594 : CollatzResearch.WordTrace tailWord_1623594 prefixEnd_1623594 833684109756025914708233 := by
  unfold tailWord_1623594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14804334520000925156075459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39478225386669133749534557 14804334520000925156075459)
  ·
    refine ⟨22206501780001387734113189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14804334520000925156075459 22206501780001387734113189)
    ·
      refine ⟨4163719083750260200146223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22206501780001387734113189 4163719083750260200146223)
      ·
        refine ⟨6245578625625390300219335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163719083750260200146223 6245578625625390300219335)
        ·
          refine ⟨9368367938438085450329003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245578625625390300219335 9368367938438085450329003)
          ·
            refine ⟨14052551907657128175493505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368367938438085450329003 14052551907657128175493505)
            ·
              refine ⟨10539413930742846131620129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14052551907657128175493505 10539413930742846131620129)
              ·
                refine ⟨7904560448057134598715097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10539413930742846131620129 7904560448057134598715097)
                ·
                  refine ⟨5928420336042850949036323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904560448057134598715097 5928420336042850949036323)
                  ·
                    refine ⟨8892630504064276423554485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5928420336042850949036323 8892630504064276423554485)
                    ·
                      refine ⟨833684109756025914708233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8892630504064276423554485 833684109756025914708233)
                      ·
                        rfl

theorem cell23_1623594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1623594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623594 prefixEnd_1623594 := by exact prefixLift 1623594
  have htrace : WordTrace (prefixWord ++ tailWord_1623594) baseStart_1623594 baseEnd_1623594 := by
    simpa [prefixWord, tailWord_1623594, baseEnd_1623594] using wordTrace_append hprefix tailTrace_1623594
  have hstable : (prefixWord ++ tailWord_1623594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623594).length < 2 ^ (prefixWord ++ tailWord_1623594).sum := by decide
  have hdescent : baseEnd_1623594 < baseStart_1623594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623657 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 8]
def baseStart_1623657 : Nat := 118140960795 + 1623657 * 2 ^ 59
def prefixEnd_1623657 : Nat := 4983230072969 + 3 ^ 40 * 1623657 * 2
def baseEnd_1623657 : Nat := 277905486345753056073481

theorem tailTrace_1623657 : CollatzResearch.WordTrace tailWord_1623657 prefixEnd_1623657 277905486345753056073481 := by
  unfold tailWord_1623657
  simp only [CollatzResearch.WordTrace]
  refine ⟨59219635878775462383845225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39479757252516974922563483 59219635878775462383845225)
  ·
    refine ⟨44414726909081596787883919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59219635878775462383845225 44414726909081596787883919)
    ·
      refine ⟨66622090363622395181825879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44414726909081596787883919 66622090363622395181825879)
      ·
        refine ⟨99933135545433592772738819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66622090363622395181825879 99933135545433592772738819)
        ·
          refine ⟨149899703318150389159108229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99933135545433592772738819 149899703318150389159108229)
          ·
            refine ⟨28106194372153197967332793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149899703318150389159108229 28106194372153197967332793)
            ·
              refine ⟨21079645779114898475499595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28106194372153197967332793 21079645779114898475499595)
              ·
                refine ⟨31619468668672347713249393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21079645779114898475499595 31619468668672347713249393)
                ·
                  refine ⟨23714601501504260784937045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31619468668672347713249393 23714601501504260784937045)
                  ·
                    refine ⟨277905486345753056073481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23714601501504260784937045 277905486345753056073481)
                    ·
                      rfl

theorem cell23_1623657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_1623657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623657 prefixEnd_1623657 := by exact prefixLift 1623657
  have htrace : WordTrace (prefixWord ++ tailWord_1623657) baseStart_1623657 baseEnd_1623657 := by
    simpa [prefixWord, tailWord_1623657, baseEnd_1623657] using wordTrace_append hprefix tailTrace_1623657
  have hstable : (prefixWord ++ tailWord_1623657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623657).length < 2 ^ (prefixWord ++ tailWord_1623657).sum := by decide
  have hdescent : baseEnd_1623657 < baseStart_1623657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623674 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_1623674 : Nat := 118140960795 + 1623674 * 2 ^ 59
def prefixEnd_1623674 : Nat := 4983230072969 + 3 ^ 40 * 1623674 * 2
def baseEnd_1623674 : Nat := 277908396069461867235955

theorem tailTrace_1623674 : CollatzResearch.WordTrace tailWord_1623674 prefixEnd_1623674 277908396069461867235955 := by
  unfold tailWord_1623674
  simp only [CollatzResearch.WordTrace]
  refine ⟨14805063979928468571803519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39480170613142582858142717 14805063979928468571803519)
  ·
    refine ⟨22207595969892702857705279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14805063979928468571803519 22207595969892702857705279)
    ·
      refine ⟨33311393954839054286557919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22207595969892702857705279 33311393954839054286557919)
      ·
        refine ⟨49967090932258581429836879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33311393954839054286557919 49967090932258581429836879)
        ·
          refine ⟨74950636398387872144755319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49967090932258581429836879 74950636398387872144755319)
          ·
            refine ⟨112425954597581808217132979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74950636398387872144755319 112425954597581808217132979)
            ·
              refine ⟨168638931896372712325699469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112425954597581808217132979 168638931896372712325699469)
              ·
                refine ⟨63239599461139767122137301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168638931896372712325699469 63239599461139767122137301)
                ·
                  refine ⟨1482178112370463291925093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63239599461139767122137301 1482178112370463291925093)
                  ·
                    refine ⟨277908396069461867235955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482178112370463291925093 277908396069461867235955)
                    ·
                      rfl

theorem cell23_1623674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_1623674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623674 prefixEnd_1623674 := by exact prefixLift 1623674
  have htrace : WordTrace (prefixWord ++ tailWord_1623674) baseStart_1623674 baseEnd_1623674 := by
    simpa [prefixWord, tailWord_1623674, baseEnd_1623674] using wordTrace_append hprefix tailTrace_1623674
  have hstable : (prefixWord ++ tailWord_1623674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623674).length < 2 ^ (prefixWord ++ tailWord_1623674).sum := by decide
  have hdescent : baseEnd_1623674 < baseStart_1623674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623681 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1623681 : Nat := 118140960795 + 1623681 * 2 ^ 59
def prefixEnd_1623681 : Nat := 4983230072969 + 3 ^ 40 * 1623681 * 2
def baseEnd_1623681 : Nat := 833728782572967074320333

theorem tailTrace_1623681 : CollatzResearch.WordTrace tailWord_1623681 prefixEnd_1623681 833728782572967074320333 := by
  unfold tailWord_1623681
  simp only [CollatzResearch.WordTrace]
  refine ⟨59220511230688514482718897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39480340820459009655145931 59220511230688514482718897)
  ·
    refine ⟨44415383423016385862039173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59220511230688514482718897 44415383423016385862039173)
    ·
      refine ⟨8327884391815572349132345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44415383423016385862039173 8327884391815572349132345)
      ·
        refine ⟨6245913293861679261849259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8327884391815572349132345 6245913293861679261849259)
        ·
          refine ⟨9368869940792518892773889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245913293861679261849259 9368869940792518892773889)
          ·
            refine ⟨7026652455594389169580417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9368869940792518892773889 7026652455594389169580417)
            ·
              refine ⟨5269989341695791877185313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026652455594389169580417 5269989341695791877185313)
              ·
                refine ⟨3952492006271843907888985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5269989341695791877185313 3952492006271843907888985)
                ·
                  refine ⟨2964369004703882930916739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3952492006271843907888985 2964369004703882930916739)
                  ·
                    refine ⟨4446553507055824396375109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2964369004703882930916739 4446553507055824396375109)
                    ·
                      refine ⟨833728782572967074320333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4446553507055824396375109 833728782572967074320333)
                      ·
                        rfl

theorem cell23_1623681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1623681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623681 prefixEnd_1623681 := by exact prefixLift 1623681
  have htrace : WordTrace (prefixWord ++ tailWord_1623681) baseStart_1623681 baseEnd_1623681 := by
    simpa [prefixWord, tailWord_1623681, baseEnd_1623681] using wordTrace_append hprefix tailTrace_1623681
  have hstable : (prefixWord ++ tailWord_1623681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623681).length < 2 ^ (prefixWord ++ tailWord_1623681).sum := by decide
  have hdescent : baseEnd_1623681 < baseStart_1623681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623708 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1623708 : Nat := 118140960795 + 1623708 * 2 ^ 59
def prefixEnd_1623708 : Nat := 4983230072969 + 3 ^ 40 * 1623708 * 2
def baseEnd_1623708 : Nat := 277914215516879489560903

theorem tailTrace_1623708 : CollatzResearch.WordTrace tailWord_1623708 prefixEnd_1623708 277914215516879489560903 := by
  unfold tailWord_1623708
  simp only [CollatzResearch.WordTrace]
  refine ⟨29610748000795349046975889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39480997334393798729301185 29610748000795349046975889)
  ·
    refine ⟨22208061000596511785231917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29610748000795349046975889 22208061000596511785231917)
    ·
      refine ⟨8328022875223691919461969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22208061000596511785231917 8328022875223691919461969)
      ·
        refine ⟨6246017156417768939596477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8328022875223691919461969 6246017156417768939596477)
        ·
          refine ⟨2342256433656663352348679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6246017156417768939596477 2342256433656663352348679)
          ·
            refine ⟨3513384650484995028523019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342256433656663352348679 3513384650484995028523019)
            ·
              refine ⟨5270076975727492542784529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513384650484995028523019 5270076975727492542784529)
              ·
                refine ⟨3952557731795619407088397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270076975727492542784529 3952557731795619407088397)
                ·
                  refine ⟨1482209149423357277658149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3952557731795619407088397 1482209149423357277658149)
                  ·
                    refine ⟨277914215516879489560903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482209149423357277658149 277914215516879489560903)
                    ·
                      rfl

theorem cell23_1623708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1623708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623708 prefixEnd_1623708 := by exact prefixLift 1623708
  have htrace : WordTrace (prefixWord ++ tailWord_1623708) baseStart_1623708 baseEnd_1623708 := by
    simpa [prefixWord, tailWord_1623708, baseEnd_1623708] using wordTrace_append hprefix tailTrace_1623708
  have hstable : (prefixWord ++ tailWord_1623708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623708).length < 2 ^ (prefixWord ++ tailWord_1623708).sum := by decide
  have hdescent : baseEnd_1623708 < baseStart_1623708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623725 : List Nat := [1, 5, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1623725 : Nat := 118140960795 + 1623725 * 2 ^ 59
def prefixEnd_1623725 : Nat := 4983230072969 + 3 ^ 40 * 1623725 * 2
def baseEnd_1623725 : Nat := 277917125240588300723377

theorem tailTrace_1623725 : CollatzResearch.WordTrace tailWord_1623725 prefixEnd_1623725 277917125240588300723377 := by
  unfold tailWord_1623725
  simp only [CollatzResearch.WordTrace]
  refine ⟨59222116042529109997320629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39481410695019406664880419 59222116042529109997320629)
  ·
    refine ⟨5552073378987104062248809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59222116042529109997320629 5552073378987104062248809)
    ·
      refine ⟨4164055034240328046686607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5552073378987104062248809 4164055034240328046686607)
      ·
        refine ⟨6246082551360492070029911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164055034240328046686607 6246082551360492070029911)
        ·
          refine ⟨9369123827040738105044867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6246082551360492070029911 9369123827040738105044867)
          ·
            refine ⟨14053685740561107157567301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369123827040738105044867 14053685740561107157567301)
            ·
              refine ⟨2635066076355207592043869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14053685740561107157567301 2635066076355207592043869)
              ·
                refine ⟨988149778633202847016451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635066076355207592043869 988149778633202847016451)
                ·
                  refine ⟨1482224667949804270524677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988149778633202847016451 1482224667949804270524677)
                  ·
                    refine ⟨277917125240588300723377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482224667949804270524677 277917125240588300723377)
                    ·
                      rfl

theorem cell23_1623725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1623725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623725 prefixEnd_1623725 := by exact prefixLift 1623725
  have htrace : WordTrace (prefixWord ++ tailWord_1623725) baseStart_1623725 baseEnd_1623725 := by
    simpa [prefixWord, tailWord_1623725, baseEnd_1623725] using wordTrace_append hprefix tailTrace_1623725
  have hstable : (prefixWord ++ tailWord_1623725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623725).length < 2 ^ (prefixWord ++ tailWord_1623725).sum := by decide
  have hdescent : baseEnd_1623725 < baseStart_1623725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623731 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 3]
def baseStart_1623731 : Nat := 118140960795 + 1623731 * 2 ^ 59
def prefixEnd_1623731 : Nat := 4983230072969 + 3 ^ 40 * 1623731 * 2
def baseEnd_1623731 : Nat := 833754456605691878695103

theorem tailTrace_1623731 : CollatzResearch.WordTrace tailWord_1623731 prefixEnd_1623731 833754456605691878695103 := by
  unfold tailWord_1623731
  simp only [CollatzResearch.WordTrace]
  refine ⟨59222334880507373022039047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39481556587004915348026031 59222334880507373022039047)
  ·
    refine ⟨88833502320761059533058571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59222334880507373022039047 88833502320761059533058571)
    ·
      refine ⟨133250253481141589299587857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88833502320761059533058571 133250253481141589299587857)
      ·
        refine ⟨99937690110856191974690893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133250253481141589299587857 99937690110856191974690893)
        ·
          refine ⟨37476633791571071990509085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99937690110856191974690893 37476633791571071990509085)
          ·
            refine ⟨14053737671839151996440907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37476633791571071990509085 14053737671839151996440907)
            ·
              refine ⟨21080606507758727994661361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14053737671839151996440907 21080606507758727994661361)
              ·
                refine ⟨15810454880819045995996021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21080606507758727994661361 15810454880819045995996021)
                ·
                  refine ⟨1482230145076785562124627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15810454880819045995996021 1482230145076785562124627)
                  ·
                    refine ⟨2223345217615178343186941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1482230145076785562124627 2223345217615178343186941)
                    ·
                      refine ⟨833754456605691878695103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2223345217615178343186941 833754456605691878695103)
                      ·
                        rfl

theorem cell23_1623731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_1623731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623731 prefixEnd_1623731 := by exact prefixLift 1623731
  have htrace : WordTrace (prefixWord ++ tailWord_1623731) baseStart_1623731 baseEnd_1623731 := by
    simpa [prefixWord, tailWord_1623731, baseEnd_1623731] using wordTrace_append hprefix tailTrace_1623731
  have hstable : (prefixWord ++ tailWord_1623731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623731).length < 2 ^ (prefixWord ++ tailWord_1623731).sum := by decide
  have hdescent : baseEnd_1623731 < baseStart_1623731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623781 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_1623781 : Nat := 118140960795 + 1623781 * 2 ^ 59
def prefixEnd_1623781 : Nat := 4983230072969 + 3 ^ 40 * 1623781 * 2
def baseEnd_1623781 : Nat := 277926710212805561023291

theorem tailTrace_1623781 : CollatzResearch.WordTrace tailWord_1623781 prefixEnd_1623781 277926710212805561023291 := by
  unfold tailWord_1623781
  simp only [CollatzResearch.WordTrace]
  refine ⟨59224158530326231561359197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39482772353550821040906131 59224158530326231561359197)
  ·
    refine ⟨22209059448872336835509699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59224158530326231561359197 22209059448872336835509699)
    ·
      refine ⟨33313589173308505253264549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22209059448872336835509699 33313589173308505253264549)
      ·
        refine ⟨6246297969995344734987103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33313589173308505253264549 6246297969995344734987103)
        ·
          refine ⟨9369446954993017102480655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6246297969995344734987103 9369446954993017102480655)
          ·
            refine ⟨14054170432489525653720983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369446954993017102480655 14054170432489525653720983)
            ·
              refine ⟨21081255648734288480581475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054170432489525653720983 21081255648734288480581475)
              ·
                refine ⟨31621883473101432720872213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21081255648734288480581475 31621883473101432720872213)
                ·
                  refine ⟨1482275787801629658790885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31621883473101432720872213 1482275787801629658790885)
                  ·
                    refine ⟨277926710212805561023291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482275787801629658790885 277926710212805561023291)
                    ·
                      rfl

theorem cell23_1623781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_1623781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623781 prefixEnd_1623781 := by exact prefixLift 1623781
  have htrace : WordTrace (prefixWord ++ tailWord_1623781) baseStart_1623781 baseEnd_1623781 := by
    simpa [prefixWord, tailWord_1623781, baseEnd_1623781] using wordTrace_append hprefix tailTrace_1623781
  have hstable : (prefixWord ++ tailWord_1623781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623781).length < 2 ^ (prefixWord ++ tailWord_1623781).sum := by decide
  have hdescent : baseEnd_1623781 < baseStart_1623781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623788 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 5, 2, 2]
def baseStart_1623788 : Nat := 118140960795 + 1623788 * 2 ^ 59
def prefixEnd_1623788 : Nat := 4983230072969 + 3 ^ 40 * 1623788 * 2
def baseEnd_1623788 : Nat := 833783725002998155682341

theorem tailTrace_1623788 : CollatzResearch.WordTrace tailWord_1623788 prefixEnd_1623788 833783725002998155682341 := by
  unfold tailWord_1623788
  simp only [CollatzResearch.WordTrace]
  refine ⟨29612206920650435878432009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39482942560867247837909345 29612206920650435878432009)
  ·
    refine ⟨22209155190487826908824007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29612206920650435878432009 22209155190487826908824007)
    ·
      refine ⟨33313732785731740363236011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22209155190487826908824007 33313732785731740363236011)
      ·
        refine ⟨49970599178597610544854017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33313732785731740363236011 49970599178597610544854017)
        ·
          refine ⟨37477949383948207908640513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49970599178597610544854017 37477949383948207908640513)
          ·
            refine ⟨28108462037961155931480385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37477949383948207908640513 28108462037961155931480385)
            ·
              refine ⟨21081346528470866948610289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28108462037961155931480385 21081346528470866948610289)
              ·
                refine ⟨15811009896353150211457717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21081346528470866948610289 15811009896353150211457717)
                ·
                  refine ⟨1482282177783107832324161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15811009896353150211457717 1482282177783107832324161)
                  ·
                    refine ⟨1111711633337330874243121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1482282177783107832324161 1111711633337330874243121)
                    ·
                      refine ⟨833783725002998155682341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111711633337330874243121 833783725002998155682341)
                      ·
                        rfl

theorem cell23_1623788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_1623788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623788 prefixEnd_1623788 := by exact prefixLift 1623788
  have htrace : WordTrace (prefixWord ++ tailWord_1623788) baseStart_1623788 baseEnd_1623788 := by
    simpa [prefixWord, tailWord_1623788, baseEnd_1623788] using wordTrace_append hprefix tailTrace_1623788
  have hstable : (prefixWord ++ tailWord_1623788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623788).length < 2 ^ (prefixWord ++ tailWord_1623788).sum := by decide
  have hdescent : baseEnd_1623788 < baseStart_1623788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623791 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_1623791 : Nat := 118140960795 + 1623791 * 2 ^ 59
def prefixEnd_1623791 : Nat := 4983230072969 + 3 ^ 40 * 1623791 * 2
def baseEnd_1623791 : Nat := 833785265444961643944827

theorem tailTrace_1623791 : CollatzResearch.WordTrace tailWord_1623791 prefixEnd_1623791 833785265444961643944827 := by
  unfold tailWord_1623791
  simp only [CollatzResearch.WordTrace]
  refine ⟨59224523260290003269223227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39483015506860002179482151 59224523260290003269223227)
  ·
    refine ⟨88836784890435004903834841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59224523260290003269223227 88836784890435004903834841)
    ·
      refine ⟨66627588667826253677876131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88836784890435004903834841 66627588667826253677876131)
      ·
        refine ⟨99941383001739380516814197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66627588667826253677876131 99941383001739380516814197)
        ·
          refine ⟨9369504656413066923451331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99941383001739380516814197 9369504656413066923451331)
          ·
            refine ⟨14054256984619600385176997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369504656413066923451331 14054256984619600385176997)
            ·
              refine ⟨2635173184616175072220687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14054256984619600385176997 2635173184616175072220687)
              ·
                refine ⟨3952759776924262608331031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635173184616175072220687 3952759776924262608331031)
                ·
                  refine ⟨5929139665386393912496547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952759776924262608331031 5929139665386393912496547)
                  ·
                    refine ⟨8893709498079590868744821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5929139665386393912496547 8893709498079590868744821)
                    ·
                      refine ⟨833785265444961643944827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8893709498079590868744821 833785265444961643944827)
                      ·
                        rfl

theorem cell23_1623791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_1623791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623791 prefixEnd_1623791 := by exact prefixLift 1623791
  have htrace : WordTrace (prefixWord ++ tailWord_1623791) baseStart_1623791 baseEnd_1623791 := by
    simpa [prefixWord, tailWord_1623791, baseEnd_1623791] using wordTrace_append hprefix tailTrace_1623791
  have hstable : (prefixWord ++ tailWord_1623791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623791).length < 2 ^ (prefixWord ++ tailWord_1623791).sum := by decide
  have hdescent : baseEnd_1623791 < baseStart_1623791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623798 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1623798 : Nat := 118140960795 + 1623798 * 2 ^ 59
def prefixEnd_1623798 : Nat := 4983230072969 + 3 ^ 40 * 1623798 * 2
def baseEnd_1623798 : Nat := 277929619936514372185765

theorem tailTrace_1623798 : CollatzResearch.WordTrace tailWord_1623798 prefixEnd_1623798 277929619936514372185765 := by
  unfold tailWord_1623798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701548660704040216545503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39483185714176428976485365 3701548660704040216545503)
  ·
    refine ⟨5552322991056060324818255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701548660704040216545503 5552322991056060324818255)
    ·
      refine ⟨8328484486584090487227383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5552322991056060324818255 8328484486584090487227383)
      ·
        refine ⟨12492726729876135730841075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8328484486584090487227383 12492726729876135730841075)
        ·
          refine ⟨18739090094814203596261613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12492726729876135730841075 18739090094814203596261613)
          ·
            refine ⟨7027158785555326348598105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18739090094814203596261613 7027158785555326348598105)
            ·
              refine ⟨5270369089166494761448579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027158785555326348598105 5270369089166494761448579)
              ·
                refine ⟨7905553633749742142172869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5270369089166494761448579 7905553633749742142172869)
                ·
                  refine ⟨1482291306328076651657413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7905553633749742142172869 1482291306328076651657413)
                  ·
                    refine ⟨277929619936514372185765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482291306328076651657413 277929619936514372185765)
                    ·
                      rfl

theorem cell23_1623798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1623798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623798 prefixEnd_1623798 := by exact prefixLift 1623798
  have htrace : WordTrace (prefixWord ++ tailWord_1623798) baseStart_1623798 baseEnd_1623798 := by
    simpa [prefixWord, tailWord_1623798, baseEnd_1623798] using wordTrace_append hprefix tailTrace_1623798
  have hstable : (prefixWord ++ tailWord_1623798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623798).length < 2 ^ (prefixWord ++ tailWord_1623798).sum := by decide
  have hdescent : baseEnd_1623798 < baseStart_1623798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623815 : List Nat := [1, 1, 4, 4, 2, 1, 1, 3, 2, 4]
def baseStart_1623815 : Nat := 118140960795 + 1623815 * 2 ^ 59
def prefixEnd_1623815 : Nat := 4983230072969 + 3 ^ 40 * 1623815 * 2
def baseEnd_1623815 : Nat := 277932529660223183348239

theorem tailTrace_1623815 : CollatzResearch.WordTrace tailWord_1623815 prefixEnd_1623815 277932529660223183348239 := by
  unfold tailWord_1623815
  simp only [CollatzResearch.WordTrace]
  refine ⟨59225398612203055368096899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39483599074802036912064599 59225398612203055368096899)
  ·
    refine ⟨88838097918304583052145349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59225398612203055368096899 88838097918304583052145349)
    ·
      refine ⟨16657143359682109322277253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88838097918304583052145349 16657143359682109322277253)
      ·
        refine ⟨3123214379940395497926985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16657143359682109322277253 3123214379940395497926985)
        ·
          refine ⟨2342410784955296623445239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3123214379940395497926985 2342410784955296623445239)
          ·
            refine ⟨3513616177432944935167859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342410784955296623445239 3513616177432944935167859)
            ·
              refine ⟨5270424266149417402751789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513616177432944935167859 5270424266149417402751789)
              ·
                refine ⟨1976409099806031526031921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5270424266149417402751789 1976409099806031526031921)
                ·
                  refine ⟨1482306824854523644523941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1976409099806031526031921 1482306824854523644523941)
                  ·
                    refine ⟨277932529660223183348239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482306824854523644523941 277932529660223183348239)
                    ·
                      rfl

theorem cell23_1623815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_1623815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623815 prefixEnd_1623815 := by exact prefixLift 1623815
  have htrace : WordTrace (prefixWord ++ tailWord_1623815) baseStart_1623815 baseEnd_1623815 := by
    simpa [prefixWord, tailWord_1623815, baseEnd_1623815] using wordTrace_append hprefix tailTrace_1623815
  have hstable : (prefixWord ++ tailWord_1623815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623815).length < 2 ^ (prefixWord ++ tailWord_1623815).sum := by decide
  have hdescent : baseEnd_1623815 < baseStart_1623815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623881 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_1623881 : Nat := 118140960795 + 1623881 * 2 ^ 59
def prefixEnd_1623881 : Nat := 4983230072969 + 3 ^ 40 * 1623881 * 2
def baseEnd_1623881 : Nat := 833831478703866291819413

theorem tailTrace_1623881 : CollatzResearch.WordTrace tailWord_1623881 prefixEnd_1623881 833831478703866291819413 := by
  unfold tailWord_1623881
  simp only [CollatzResearch.WordTrace]
  refine ⟨59227805829963948639999497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39485203886642632426666331 59227805829963948639999497)
  ·
    refine ⟨44420854372472961479999623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59227805829963948639999497 44420854372472961479999623)
    ·
      refine ⟨66631281558709442219999435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44420854372472961479999623 66631281558709442219999435)
      ·
        refine ⟨99946922338064163329999153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66631281558709442219999435 99946922338064163329999153)
        ·
          refine ⟨74960191753548122497499365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99946922338064163329999153 74960191753548122497499365)
          ·
            refine ⟨14055035953790272968281131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74960191753548122497499365 14055035953790272968281131)
            ·
              refine ⟨21082553930685409452421697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14055035953790272968281131 21082553930685409452421697)
              ·
                refine ⟨15811915448014057089316273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21082553930685409452421697 15811915448014057089316273)
                ·
                  refine ⟨11858936586010542816987205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15811915448014057089316273 11858936586010542816987205)
                  ·
                    refine ⟨2223550609876976778185101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11858936586010542816987205 2223550609876976778185101)
                    ·
                      refine ⟨833831478703866291819413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2223550609876976778185101 833831478703866291819413)
                      ·
                        rfl

theorem cell23_1623881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_1623881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623881 prefixEnd_1623881 := by exact prefixLift 1623881
  have htrace : WordTrace (prefixWord ++ tailWord_1623881) baseStart_1623881 baseEnd_1623881 := by
    simpa [prefixWord, tailWord_1623881, baseEnd_1623881] using wordTrace_append hprefix tailTrace_1623881
  have hstable : (prefixWord ++ tailWord_1623881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623881).length < 2 ^ (prefixWord ++ tailWord_1623881).sum := by decide
  have hdescent : baseEnd_1623881 < baseStart_1623881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623918 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_1623918 : Nat := 118140960795 + 1623918 * 2 ^ 59
def prefixEnd_1623918 : Nat := 4983230072969 + 3 ^ 40 * 1623918 * 2
def baseEnd_1623918 : Nat := 92650053054231405228527

theorem tailTrace_1623918 : CollatzResearch.WordTrace tailWord_1623918 prefixEnd_1623918 92650053054231405228527 := by
  unfold tailWord_1623918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403644416353737994887051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39486103553886602639397605 7403644416353737994887051)
  ·
    refine ⟨11105466624530606992330577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7403644416353737994887051 11105466624530606992330577)
    ·
      refine ⟨8329099968397955244247933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11105466624530606992330577 8329099968397955244247933)
      ·
        refine ⟨3123412488149233216592975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8329099968397955244247933 3123412488149233216592975)
        ·
          refine ⟨4685118732223849824889463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123412488149233216592975 4685118732223849824889463)
          ·
            refine ⟨7027678098335774737334195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685118732223849824889463 7027678098335774737334195)
            ·
              refine ⟨10541517147503662106001293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027678098335774737334195 10541517147503662106001293)
              ·
                refine ⟨3953068930313873289750485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10541517147503662106001293 3953068930313873289750485)
                ·
                  refine ⟨92650053054231405228527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3953068930313873289750485 92650053054231405228527)
                  ·
                    rfl

theorem cell23_1623918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_1623918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1623918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1623918 prefixEnd_1623918 := by exact prefixLift 1623918
  have htrace : WordTrace (prefixWord ++ tailWord_1623918) baseStart_1623918 baseEnd_1623918 := by
    simpa [prefixWord, tailWord_1623918, baseEnd_1623918] using wordTrace_append hprefix tailTrace_1623918
  have hstable : (prefixWord ++ tailWord_1623918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623918).length < 2 ^ (prefixWord ++ tailWord_1623918).sum := by decide
  have hdescent : baseEnd_1623918 < baseStart_1623918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624025 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 6]
def baseStart_1624025 : Nat := 118140960795 + 1624025 * 2 ^ 59
def prefixEnd_1624025 : Nat := 4983230072969 + 3 ^ 40 * 1624025 * 2
def baseEnd_1624025 : Nat := 92656157768679303157639

theorem tailTrace_1624025 : CollatzResearch.WordTrace tailWord_1624025 prefixEnd_1624025 92656157768679303157639 := by
  unfold tailWord_1624025
  simp only [CollatzResearch.WordTrace]
  refine ⟨59233057941442261233241529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39488705294294840822161019 59233057941442261233241529)
  ·
    refine ⟨44424793456081695924931147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59233057941442261233241529 44424793456081695924931147)
    ·
      refine ⟨66637190184122543887396721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44424793456081695924931147 66637190184122543887396721)
      ·
        refine ⟨49977892638091907915547541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66637190184122543887396721 49977892638091907915547541)
        ·
          refine ⟨2342713717410558183541291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49977892638091907915547541 2342713717410558183541291)
          ·
            refine ⟨3514070576115837275311937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342713717410558183541291 3514070576115837275311937)
            ·
              refine ⟨2635552932086877956483953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514070576115837275311937 2635552932086877956483953)
              ·
                refine ⟨1976664699065158467362965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635552932086877956483953 1976664699065158467362965)
                ·
                  refine ⟨92656157768679303157639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1976664699065158467362965 92656157768679303157639)
                  ·
                    rfl

theorem cell23_1624025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 6].length) (baseStart_1624025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624025 prefixEnd_1624025 := by exact prefixLift 1624025
  have htrace : WordTrace (prefixWord ++ tailWord_1624025) baseStart_1624025 baseEnd_1624025 := by
    simpa [prefixWord, tailWord_1624025, baseEnd_1624025] using wordTrace_append hprefix tailTrace_1624025
  have hstable : (prefixWord ++ tailWord_1624025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624025).length < 2 ^ (prefixWord ++ tailWord_1624025).sum := by decide
  have hdescent : baseEnd_1624025 < baseStart_1624025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624029 : List Nat := [1, 4, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1624029 : Nat := 118140960795 + 1624029 * 2 ^ 59
def prefixEnd_1624029 : Nat := 4983230072969 + 3 ^ 40 * 1624029 * 2
def baseEnd_1624029 : Nat := 277969157946910570922911

theorem tailTrace_1624029 : CollatzResearch.WordTrace tailWord_1624029 prefixEnd_1624029 277969157946910570922911 := by
  unfold tailWord_1624029
  simp only [CollatzResearch.WordTrace]
  refine ⟨59233203833427769916387141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39488802555618513277591427 59233203833427769916387141)
  ·
    refine ⟨11106225718767706859322589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59233203833427769916387141 11106225718767706859322589)
    ·
      refine ⟨4164834644537890072245971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11106225718767706859322589 4164834644537890072245971)
      ·
        refine ⟨6247251966806835108368957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4164834644537890072245971 6247251966806835108368957)
        ·
          refine ⟨2342719487552563165638359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6247251966806835108368957 2342719487552563165638359)
          ·
            refine ⟨3514079231328844748457539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342719487552563165638359 3514079231328844748457539)
            ·
              refine ⟨5271118846993267122686309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514079231328844748457539 5271118846993267122686309)
              ·
                refine ⟨988334783811237585503683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5271118846993267122686309 988334783811237585503683)
                ·
                  refine ⟨1482502175716856378255525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988334783811237585503683 1482502175716856378255525)
                  ·
                    refine ⟨277969157946910570922911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482502175716856378255525 277969157946910570922911)
                    ·
                      rfl

theorem cell23_1624029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1624029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624029 prefixEnd_1624029 := by exact prefixLift 1624029
  have htrace : WordTrace (prefixWord ++ tailWord_1624029) baseStart_1624029 baseEnd_1624029 := by
    simpa [prefixWord, tailWord_1624029, baseEnd_1624029] using wordTrace_append hprefix tailTrace_1624029
  have hstable : (prefixWord ++ tailWord_1624029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624029).length < 2 ^ (prefixWord ++ tailWord_1624029).sum := by decide
  have hdescent : baseEnd_1624029 < baseStart_1624029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624069 : List Nat := [1, 3, 1, 1, 2, 5, 2, 3, 1, 1, 3]
def baseStart_1624069 : Nat := 118140960795 + 1624069 * 2 ^ 59
def prefixEnd_1624069 : Nat := 4983230072969 + 3 ^ 40 * 1624069 * 2
def baseEnd_1624069 : Nat := 833928013066911556268549

theorem tailTrace_1624069 : CollatzResearch.WordTrace tailWord_1624069 prefixEnd_1624069 833928013066911556268549 := by
  unfold tailWord_1624069
  simp only [CollatzResearch.WordTrace]
  refine ⟨59234662753282856747843261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39489775168855237831895507 59234662753282856747843261)
  ·
    refine ⟨22212998532481071280441223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59234662753282856747843261 22212998532481071280441223)
    ·
      refine ⟨33319497798721606920661835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22212998532481071280441223 33319497798721606920661835)
      ·
        refine ⟨49979246698082410380992753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33319497798721606920661835 49979246698082410380992753)
        ·
          refine ⟨37484435023561807785744565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49979246698082410380992753 37484435023561807785744565)
          ·
            refine ⟨3514165783458919479913553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37484435023561807785744565 3514165783458919479913553)
            ·
              refine ⟨2635624337594189609935165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514165783458919479913553 2635624337594189609935165)
              ·
                refine ⟨988359126597821103725687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635624337594189609935165 988359126597821103725687)
                ·
                  refine ⟨1482538689896731655588531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988359126597821103725687 1482538689896731655588531)
                  ·
                    refine ⟨2223808034845097483382797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1482538689896731655588531 2223808034845097483382797)
                    ·
                      refine ⟨833928013066911556268549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2223808034845097483382797 833928013066911556268549)
                      ·
                        rfl

theorem cell23_1624069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_1624069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624069 prefixEnd_1624069 := by exact prefixLift 1624069
  have htrace : WordTrace (prefixWord ++ tailWord_1624069) baseStart_1624069 baseEnd_1624069 := by
    simpa [prefixWord, tailWord_1624069, baseEnd_1624069] using wordTrace_append hprefix tailTrace_1624069
  have hstable : (prefixWord ++ tailWord_1624069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624069).length < 2 ^ (prefixWord ++ tailWord_1624069).sum := by decide
  have hdescent : baseEnd_1624069 < baseStart_1624069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624075 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 4]
def baseStart_1624075 : Nat := 118140960795 + 1624075 * 2 ^ 59
def prefixEnd_1624075 : Nat := 4983230072969 + 3 ^ 40 * 1624075 * 2
def baseEnd_1624075 : Nat := 833931093950838532793521

theorem tailTrace_1624075 : CollatzResearch.WordTrace tailWord_1624075 prefixEnd_1624075 833931093950838532793521 := by
  unfold tailWord_1624075
  simp only [CollatzResearch.WordTrace]
  refine ⟨59234881591261119772561679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39489921060840746515041119 59234881591261119772561679)
  ·
    refine ⟨88852322386891679658842519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59234881591261119772561679 88852322386891679658842519)
    ·
      refine ⟨133278483580337519488263779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88852322386891679658842519 133278483580337519488263779)
      ·
        refine ⟨199917725370506279232395669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133278483580337519488263779 199917725370506279232395669)
        ·
          refine ⟨9371143376742481839018547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199917725370506279232395669 9371143376742481839018547)
          ·
            refine ⟨14056715065113722758527821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371143376742481839018547 14056715065113722758527821)
            ·
              refine ⟨5271268149417646034447933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14056715065113722758527821 5271268149417646034447933)
              ·
                refine ⟨1976725556031617262917975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5271268149417646034447933 1976725556031617262917975)
                ·
                  refine ⟨2965088334047425894376963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976725556031617262917975 2965088334047425894376963)
                  ·
                    refine ⟨4447632501071138841565445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2965088334047425894376963 4447632501071138841565445)
                    ·
                      refine ⟨833931093950838532793521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4447632501071138841565445 833931093950838532793521)
                      ·
                        rfl

theorem cell23_1624075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 4].length) (baseStart_1624075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624075 prefixEnd_1624075 := by exact prefixLift 1624075
  have htrace : WordTrace (prefixWord ++ tailWord_1624075) baseStart_1624075 baseEnd_1624075 := by
    simpa [prefixWord, tailWord_1624075, baseEnd_1624075] using wordTrace_append hprefix tailTrace_1624075
  have hstable : (prefixWord ++ tailWord_1624075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624075).length < 2 ^ (prefixWord ++ tailWord_1624075).sum := by decide
  have hdescent : baseEnd_1624075 < baseStart_1624075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624088 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1624088 : Nat := 118140960795 + 1624088 * 2 ^ 59
def prefixEnd_1624088 : Nat := 4983230072969 + 3 ^ 40 * 1624088 * 2
def baseEnd_1624088 : Nat := 833937769199346981930961

theorem tailTrace_1624088 : CollatzResearch.WordTrace tailWord_1624088 prefixEnd_1624088 833937769199346981930961 := by
  unfold tailWord_1624088
  simp only [CollatzResearch.WordTrace]
  refine ⟨29617677870107011496392459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39490237160142681995189945 29617677870107011496392459)
  ·
    refine ⟨44426516805160517244588689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29617677870107011496392459 44426516805160517244588689)
    ·
      refine ⟨33319887603870387933441517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44426516805160517244588689 33319887603870387933441517)
      ·
        refine ⟨12494957851451395475040569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33319887603870387933441517 12494957851451395475040569)
        ·
          refine ⟨9371218388588546606280427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12494957851451395475040569 9371218388588546606280427)
          ·
            refine ⟨14056827582882819909420641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371218388588546606280427 14056827582882819909420641)
            ·
              refine ⟨10542620687162114932065481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14056827582882819909420641 10542620687162114932065481)
              ·
                refine ⟨7906965515371586199049111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10542620687162114932065481 7906965515371586199049111)
                ·
                  refine ⟨11860448273057379298573667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7906965515371586199049111 11860448273057379298573667)
                  ·
                    refine ⟨17790672409586068947860501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11860448273057379298573667 17790672409586068947860501)
                    ·
                      refine ⟨833937769199346981930961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17790672409586068947860501 833937769199346981930961)
                      ·
                        rfl

theorem cell23_1624088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1624088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624088 prefixEnd_1624088 := by exact prefixLift 1624088
  have htrace : WordTrace (prefixWord ++ tailWord_1624088) baseStart_1624088 baseEnd_1624088 := by
    simpa [prefixWord, tailWord_1624088, baseEnd_1624088] using wordTrace_append hprefix tailTrace_1624088
  have hstable : (prefixWord ++ tailWord_1624088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624088).length < 2 ^ (prefixWord ++ tailWord_1624088).sum := by decide
  have hdescent : baseEnd_1624088 < baseStart_1624088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624098 : List Nat := [3, 3, 1, 1, 1, 2, 2, 10]
def baseStart_1624098 : Nat := 118140960795 + 1624098 * 2 ^ 59
def prefixEnd_1624098 : Nat := 4983230072969 + 3 ^ 40 * 1624098 * 2
def baseEnd_1624098 : Nat := 30886774222440442326145

theorem tailTrace_1624098 : CollatzResearch.WordTrace tailWord_1624098 prefixEnd_1624098 30886774222440442326145 := by
  unfold tailWord_1624098
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808930117544448675162237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39490480313451863133765965 14808930117544448675162237)
  ·
    refine ⟨5553348794079168253185839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14808930117544448675162237 5553348794079168253185839)
    ·
      refine ⟨8330023191118752379778759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5553348794079168253185839 8330023191118752379778759)
      ·
        refine ⟨12495034786678128569668139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8330023191118752379778759 12495034786678128569668139)
        ·
          refine ⟨18742552180017192854502209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12495034786678128569668139 18742552180017192854502209)
          ·
            refine ⟨14056914135012894640876657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18742552180017192854502209 14056914135012894640876657)
            ·
              refine ⟨10542685601259670980657493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14056914135012894640876657 10542685601259670980657493)
              ·
                refine ⟨30886774222440442326145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10542685601259670980657493 30886774222440442326145)
                ·
                  rfl

theorem cell23_1624098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_1624098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624098 prefixEnd_1624098 := by exact prefixLift 1624098
  have htrace : WordTrace (prefixWord ++ tailWord_1624098) baseStart_1624098 baseEnd_1624098 := by
    simpa [prefixWord, tailWord_1624098, baseEnd_1624098] using wordTrace_append hprefix tailTrace_1624098
  have hstable : (prefixWord ++ tailWord_1624098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624098).length < 2 ^ (prefixWord ++ tailWord_1624098).sum := by decide
  have hdescent : baseEnd_1624098 < baseStart_1624098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624112 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3]
def baseStart_1624112 : Nat := 118140960795 + 1624112 * 2 ^ 59
def prefixEnd_1624112 : Nat := 4983230072969 + 3 ^ 40 * 1624112 * 2
def baseEnd_1624112 : Nat := 833950092735054888030851

theorem tailTrace_1624112 : CollatzResearch.WordTrace tailWord_1624112 prefixEnd_1624112 833950092735054888030851 := by
  unfold tailWord_1624112
  simp only [CollatzResearch.WordTrace]
  refine ⟨29618115546063537545829295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39490820728084716727772393 29618115546063537545829295)
  ·
    refine ⟨44427173319095306318743943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29618115546063537545829295 44427173319095306318743943)
    ·
      refine ⟨66640759978642959478115915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44427173319095306318743943 66640759978642959478115915)
      ·
        refine ⟨99961139967964439217173873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66640759978642959478115915 99961139967964439217173873)
        ·
          refine ⟨74970854975973329412880405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99961139967964439217173873 74970854975973329412880405)
          ·
            refine ⟨3514258826998749816228769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74970854975973329412880405 3514258826998749816228769)
            ·
              refine ⟨2635694120249062362171577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514258826998749816228769 2635694120249062362171577)
              ·
                refine ⟨1976770590186796771628683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635694120249062362171577 1976770590186796771628683)
                ·
                  refine ⟨2965155885280195157443025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976770590186796771628683 2965155885280195157443025)
                  ·
                    refine ⟨2223866913960146368082269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965155885280195157443025 2223866913960146368082269)
                    ·
                      refine ⟨833950092735054888030851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2223866913960146368082269 833950092735054888030851)
                      ·
                        rfl

theorem cell23_1624112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_1624112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624112 prefixEnd_1624112 := by exact prefixLift 1624112
  have htrace : WordTrace (prefixWord ++ tailWord_1624112) baseStart_1624112 baseEnd_1624112 := by
    simpa [prefixWord, tailWord_1624112, baseEnd_1624112] using wordTrace_append hprefix tailTrace_1624112
  have hstable : (prefixWord ++ tailWord_1624112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624112).length < 2 ^ (prefixWord ++ tailWord_1624112).sum := by decide
  have hdescent : baseEnd_1624112 < baseStart_1624112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624125 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1624125 : Nat := 118140960795 + 1624125 * 2 ^ 59
def prefixEnd_1624125 : Nat := 4983230072969 + 3 ^ 40 * 1624125 * 2
def baseEnd_1624125 : Nat := 833956767983563337168291

theorem tailTrace_1624125 : CollatzResearch.WordTrace tailWord_1624125 prefixEnd_1624125 833956767983563337168291 := by
  unfold tailWord_1624125
  simp only [CollatzResearch.WordTrace]
  refine ⟨59236705241079978311881829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39491136827386652207921219 59236705241079978311881829)
  ·
    refine ⟨11106882232702495933477843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59236705241079978311881829 11106882232702495933477843)
    ·
      refine ⟨16660323349053743900216765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11106882232702495933477843 16660323349053743900216765)
      ·
        refine ⟨6247621255895153962581287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16660323349053743900216765 6247621255895153962581287)
        ·
          refine ⟨9371431883842730943871931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247621255895153962581287 9371431883842730943871931)
          ·
            refine ⟨14057147825764096415807897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371431883842730943871931 14057147825764096415807897)
            ·
              refine ⟨10542860869323072311855923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14057147825764096415807897 10542860869323072311855923)
              ·
                refine ⟨15814291303984608467783885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10542860869323072311855923 15814291303984608467783885)
                ·
                  refine ⟨5930359238994228175418957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15814291303984608467783885 5930359238994228175418957)
                  ·
                    refine ⟨2223884714622835565782109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5930359238994228175418957 2223884714622835565782109)
                    ·
                      refine ⟨833956767983563337168291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2223884714622835565782109 833956767983563337168291)
                      ·
                        rfl

theorem cell23_1624125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1624125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624125 prefixEnd_1624125 := by exact prefixLift 1624125
  have htrace : WordTrace (prefixWord ++ tailWord_1624125) baseStart_1624125 baseEnd_1624125 := by
    simpa [prefixWord, tailWord_1624125, baseEnd_1624125] using wordTrace_append hprefix tailTrace_1624125
  have hstable : (prefixWord ++ tailWord_1624125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624125).length < 2 ^ (prefixWord ++ tailWord_1624125).sum := by decide
  have hdescent : baseEnd_1624125 < baseStart_1624125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624138 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1624138 : Nat := 118140960795 + 1624138 * 2 ^ 59
def prefixEnd_1624138 : Nat := 4983230072969 + 3 ^ 40 * 1624138 * 2
def baseEnd_1624138 : Nat := 833963443232071786305731

theorem tailTrace_1624138 : CollatzResearch.WordTrace tailWord_1624138 prefixEnd_1624138 833963443232071786305731 := by
  unfold tailWord_1624138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809294847508220383026267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39491452926688587688070045 14809294847508220383026267)
  ·
    refine ⟨22213942271262330574539401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14809294847508220383026267 22213942271262330574539401)
    ·
      refine ⟨16660456703446747930904551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22213942271262330574539401 16660456703446747930904551)
      ·
        refine ⟨24990685055170121896356827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16660456703446747930904551 24990685055170121896356827)
        ·
          refine ⟨37486027582755182844535241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24990685055170121896356827 37486027582755182844535241)
          ·
            refine ⟨28114520687066387133401431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37486027582755182844535241 28114520687066387133401431)
            ·
              refine ⟨42171781030599580700102147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28114520687066387133401431 42171781030599580700102147)
              ·
                refine ⟨63257671545899371050153221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42171781030599580700102147 63257671545899371050153221)
                ·
                  refine ⟨11860813414856132071903729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63257671545899371050153221 11860813414856132071903729)
                  ·
                    refine ⟨8895610061142099053927797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11860813414856132071903729 8895610061142099053927797)
                    ·
                      refine ⟨833963443232071786305731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8895610061142099053927797 833963443232071786305731)
                      ·
                        rfl

theorem cell23_1624138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1624138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624138 prefixEnd_1624138 := by exact prefixLift 1624138
  have htrace : WordTrace (prefixWord ++ tailWord_1624138) baseStart_1624138 baseEnd_1624138 := by
    simpa [prefixWord, tailWord_1624138, baseEnd_1624138] using wordTrace_append hprefix tailTrace_1624138
  have hstable : (prefixWord ++ tailWord_1624138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624138).length < 2 ^ (prefixWord ++ tailWord_1624138).sum := by decide
  have hdescent : baseEnd_1624138 < baseStart_1624138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624142 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_1624142 : Nat := 118140960795 + 1624142 * 2 ^ 59
def prefixEnd_1624142 : Nat := 4983230072969 + 3 ^ 40 * 1624142 * 2
def baseEnd_1624142 : Nat := 833965497154689770655713

theorem tailTrace_1624142 : CollatzResearch.WordTrace tailWord_1624142 prefixEnd_1624142 833965497154689770655713 := by
  unfold tailWord_1624142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404665660252298776906335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39491550188012260143500453 7404665660252298776906335)
  ·
    refine ⟨11106998490378448165359503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7404665660252298776906335 11106998490378448165359503)
    ·
      refine ⟨16660497735567672248039255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11106998490378448165359503 16660497735567672248039255)
      ·
        refine ⟨24990746603351508372058883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16660497735567672248039255 24990746603351508372058883)
        ·
          refine ⟨37486119905027262558088325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24990746603351508372058883 37486119905027262558088325)
          ·
            refine ⟨7028647482192611729641561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37486119905027262558088325 7028647482192611729641561)
            ·
              refine ⟨5271485611644458797231171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7028647482192611729641561 5271485611644458797231171)
              ·
                refine ⟨7907228417466688195846757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271485611644458797231171 7907228417466688195846757)
                ·
                  refine ⟨1482605328275004036721267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7907228417466688195846757 1482605328275004036721267)
                  ·
                    refine ⟨2223907992412506055081901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1482605328275004036721267 2223907992412506055081901)
                    ·
                      refine ⟨833965497154689770655713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2223907992412506055081901 833965497154689770655713)
                      ·
                        rfl

theorem cell23_1624142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_1624142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624142 prefixEnd_1624142 := by exact prefixLift 1624142
  have htrace : WordTrace (prefixWord ++ tailWord_1624142) baseStart_1624142 baseEnd_1624142 := by
    simpa [prefixWord, tailWord_1624142, baseEnd_1624142] using wordTrace_append hprefix tailTrace_1624142
  have hstable : (prefixWord ++ tailWord_1624142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624142).length < 2 ^ (prefixWord ++ tailWord_1624142).sum := by decide
  have hdescent : baseEnd_1624142 < baseStart_1624142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624185 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1624185 : Nat := 118140960795 + 1624185 * 2 ^ 59
def prefixEnd_1624185 : Nat := 4983230072969 + 3 ^ 40 * 1624185 * 2
def baseEnd_1624185 : Nat := 833987576822833102418015

theorem tailTrace_1624185 : CollatzResearch.WordTrace tailWord_1624185 prefixEnd_1624185 833987576822833102418015 := by
  unfold tailWord_1624185
  simp only [CollatzResearch.WordTrace]
  refine ⟨59238893620862608559066009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39492595747241739039377339 59238893620862608559066009)
  ·
    refine ⟨44429170215646956419299507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59238893620862608559066009 44429170215646956419299507)
    ·
      refine ⟨66643755323470434628949261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44429170215646956419299507 66643755323470434628949261)
      ·
        refine ⟨24991408246301412985855973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66643755323470434628949261 24991408246301412985855973)
        ·
          refine ⟨4685889046181514934847995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24991408246301412985855973 4685889046181514934847995)
          ·
            refine ⟨7028833569272272402271993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685889046181514934847995 7028833569272272402271993)
            ·
              refine ⟨5271625176954204301703995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7028833569272272402271993 5271625176954204301703995)
              ·
                refine ⟨7907437765431306452555993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271625176954204301703995 7907437765431306452555993)
                ·
                  refine ⟨5930578324073479839416995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7907437765431306452555993 5930578324073479839416995)
                  ·
                    refine ⟨8895867486110219759125493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5930578324073479839416995 8895867486110219759125493)
                    ·
                      refine ⟨833987576822833102418015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8895867486110219759125493 833987576822833102418015)
                      ·
                        rfl

theorem cell23_1624185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1624185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624185 prefixEnd_1624185 := by exact prefixLift 1624185
  have htrace : WordTrace (prefixWord ++ tailWord_1624185) baseStart_1624185 baseEnd_1624185 := by
    simpa [prefixWord, tailWord_1624185, baseEnd_1624185] using wordTrace_append hprefix tailTrace_1624185
  have hstable : (prefixWord ++ tailWord_1624185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624185).length < 2 ^ (prefixWord ++ tailWord_1624185).sum := by decide
  have hdescent : baseEnd_1624185 < baseStart_1624185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624199 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_1624199 : Nat := 118140960795 + 1624199 * 2 ^ 59
def prefixEnd_1624199 : Nat := 4983230072969 + 3 ^ 40 * 1624199 * 2
def baseEnd_1624199 : Nat := 833994765551996047642951

theorem tailTrace_1624199 : CollatzResearch.WordTrace tailWord_1624199 prefixEnd_1624199 833994765551996047642951 := by
  unfold tailWord_1624199
  simp only [CollatzResearch.WordTrace]
  refine ⟨59239404242811888950075651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39492936161874592633383767 59239404242811888950075651)
  ·
    refine ⟨88859106364217833425113477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59239404242811888950075651 88859106364217833425113477)
    ·
      refine ⟨16661082443290843767208777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88859106364217833425113477 16661082443290843767208777)
      ·
        refine ⟨12495811832468132825406583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16661082443290843767208777 12495811832468132825406583)
        ·
          refine ⟨18743717748702199238109875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12495811832468132825406583 18743717748702199238109875)
          ·
            refine ⟨28115576623053298857164813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18743717748702199238109875 28115576623053298857164813)
            ·
              refine ⟨10543341233644987071436805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28115576623053298857164813 10543341233644987071436805)
              ·
                refine ⟨1976876481308435075894401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10543341233644987071436805 1976876481308435075894401)
                ·
                  refine ⟨1482657360981326306920801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1976876481308435075894401 1482657360981326306920801)
                  ·
                    refine ⟨1111993020735994730190601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1482657360981326306920801 1111993020735994730190601)
                    ·
                      refine ⟨833994765551996047642951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1111993020735994730190601 833994765551996047642951)
                      ·
                        rfl

theorem cell23_1624199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_1624199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624199 prefixEnd_1624199 := by exact prefixLift 1624199
  have htrace : WordTrace (prefixWord ++ tailWord_1624199) baseStart_1624199 baseEnd_1624199 := by
    simpa [prefixWord, tailWord_1624199, baseEnd_1624199] using wordTrace_append hprefix tailTrace_1624199
  have hstable : (prefixWord ++ tailWord_1624199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624199).length < 2 ^ (prefixWord ++ tailWord_1624199).sum := by decide
  have hdescent : baseEnd_1624199 < baseStart_1624199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624255 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_1624255 : Nat := 118140960795 + 1624255 * 2 ^ 59
def prefixEnd_1624255 : Nat := 4983230072969 + 3 ^ 40 * 1624255 * 2
def baseEnd_1624255 : Nat := 834023520468647828542693

theorem tailTrace_1624255 : CollatzResearch.WordTrace tailWord_1624255 prefixEnd_1624255 834023520468647828542693 := by
  unfold tailWord_1624255
  simp only [CollatzResearch.WordTrace]
  refine ⟨59241446730609010514114219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39494297820406007009409479 59241446730609010514114219)
  ·
    refine ⟨88862170095913515771171329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59241446730609010514114219 88862170095913515771171329)
    ·
      refine ⟨66646627571935136828378497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88862170095913515771171329 66646627571935136828378497)
      ·
        refine ⟨49984970678951352621283873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66646627571935136828378497 49984970678951352621283873)
        ·
          refine ⟨37488728009213514465962905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49984970678951352621283873 37488728009213514465962905)
          ·
            refine ⟨28116546006910135849472179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37488728009213514465962905 28116546006910135849472179)
            ·
              refine ⟨42174819010365203774208269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28116546006910135849472179 42174819010365203774208269)
              ·
                refine ⟨15815557128886951415328101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42174819010365203774208269 15815557128886951415328101)
                ·
                  refine ⟨2965416961666303390374019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15815557128886951415328101 2965416961666303390374019)
                  ·
                    refine ⟨4448125442499455085561029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2965416961666303390374019 4448125442499455085561029)
                    ·
                      refine ⟨834023520468647828542693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4448125442499455085561029 834023520468647828542693)
                      ·
                        rfl

theorem cell23_1624255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_1624255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624255 prefixEnd_1624255 := by exact prefixLift 1624255
  have htrace : WordTrace (prefixWord ++ tailWord_1624255) baseStart_1624255 baseEnd_1624255 := by
    simpa [prefixWord, tailWord_1624255, baseEnd_1624255] using wordTrace_append hprefix tailTrace_1624255
  have hstable : (prefixWord ++ tailWord_1624255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624255).length < 2 ^ (prefixWord ++ tailWord_1624255).sum := by decide
  have hdescent : baseEnd_1624255 < baseStart_1624255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624282 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_1624282 : Nat := 118140960795 + 1624282 * 2 ^ 59
def prefixEnd_1624282 : Nat := 4983230072969 + 3 ^ 40 * 1624282 * 2
def baseEnd_1624282 : Nat := 278012461482106407635023

theorem tailTrace_1624282 : CollatzResearch.WordTrace tailWord_1624282 prefixEnd_1624282 278012461482106407635023 := by
  unfold tailWord_1624282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14810607875377798531336775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39494954334340796083564733 14810607875377798531336775)
  ·
    refine ⟨22215911813066697797005163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14810607875377798531336775 22215911813066697797005163)
    ·
      refine ⟨33323867719600046695507745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22215911813066697797005163 33323867719600046695507745)
      ·
        refine ⟨24992900789700035021630809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33323867719600046695507745 24992900789700035021630809)
        ·
          refine ⟨18744675592275026266223107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24992900789700035021630809 18744675592275026266223107)
          ·
            refine ⟨28117013388412539399334661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18744675592275026266223107 28117013388412539399334661)
            ·
              refine ⟨5271940010327351137375249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28117013388412539399334661 5271940010327351137375249)
              ·
                refine ⟨3953955007745513353031437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5271940010327351137375249 3953955007745513353031437)
                ·
                  refine ⟨1482733127904567507386789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3953955007745513353031437 1482733127904567507386789)
                  ·
                    refine ⟨278012461482106407635023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482733127904567507386789 278012461482106407635023)
                    ·
                      rfl

theorem cell23_1624282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_1624282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624282 prefixEnd_1624282 := by exact prefixLift 1624282
  have htrace : WordTrace (prefixWord ++ tailWord_1624282) baseStart_1624282 baseEnd_1624282 := by
    simpa [prefixWord, tailWord_1624282, baseEnd_1624282] using wordTrace_append hprefix tailTrace_1624282
  have hstable : (prefixWord ++ tailWord_1624282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624282).length < 2 ^ (prefixWord ++ tailWord_1624282).sum := by decide
  have hdescent : baseEnd_1624282 < baseStart_1624282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624290 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1624290 : Nat := 118140960795 + 1624290 * 2 ^ 59
def prefixEnd_1624290 : Nat := 4983230072969 + 3 ^ 40 * 1624290 * 2
def baseEnd_1624290 : Nat := 92671276921283910178337

theorem tailTrace_1624290 : CollatzResearch.WordTrace tailWord_1624290 prefixEnd_1624290 92671276921283910178337 := by
  unfold tailWord_1624290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14810680821370552872909581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39495148856988140994425549 14810680821370552872909581)
  ·
    refine ⟨5554005308013957327341093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14810680821370552872909581 5554005308013957327341093)
    ·
      refine ⟨1041375995252616998876455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5554005308013957327341093 1041375995252616998876455)
      ·
        refine ⟨1562063992878925498314683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041375995252616998876455 1562063992878925498314683)
        ·
          refine ⟨2343095989318388247472025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562063992878925498314683 2343095989318388247472025)
          ·
            refine ⟨1757321991988791185604019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343095989318388247472025 1757321991988791185604019)
            ·
              refine ⟨2635982987983186778406029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757321991988791185604019 2635982987983186778406029)
              ·
                refine ⟨988493620493695041902261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635982987983186778406029 988493620493695041902261)
                ·
                  refine ⟨92671276921283910178337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 988493620493695041902261 92671276921283910178337)
                  ·
                    rfl

theorem cell23_1624290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1624290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624290 prefixEnd_1624290 := by exact prefixLift 1624290
  have htrace : WordTrace (prefixWord ++ tailWord_1624290) baseStart_1624290 baseEnd_1624290 := by
    simpa [prefixWord, tailWord_1624290, baseEnd_1624290] using wordTrace_append hprefix tailTrace_1624290
  have hstable : (prefixWord ++ tailWord_1624290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624290).length < 2 ^ (prefixWord ++ tailWord_1624290).sum := by decide
  have hdescent : baseEnd_1624290 < baseStart_1624290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624292 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_1624292 : Nat := 118140960795 + 1624292 * 2 ^ 59
def prefixEnd_1624292 : Nat := 4983230072969 + 3 ^ 40 * 1624292 * 2
def baseEnd_1624292 : Nat := 834042519252864183780023

theorem tailTrace_1624292 : CollatzResearch.WordTrace tailWord_1624292 prefixEnd_1624292 834042519252864183780023 := by
  unfold tailWord_1624292
  simp only [CollatzResearch.WordTrace]
  refine ⟨29621398115737482916605565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39495197487649977222140753 29621398115737482916605565)
  ·
    refine ⟨11108024293401556093727087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29621398115737482916605565 11108024293401556093727087)
    ·
      refine ⟨16662036440102334140590631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11108024293401556093727087 16662036440102334140590631)
      ·
        refine ⟨24993054660153501210885947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16662036440102334140590631 24993054660153501210885947)
        ·
          refine ⟨37489581990230251816328921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24993054660153501210885947 37489581990230251816328921)
          ·
            refine ⟨28117186492672688862246691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37489581990230251816328921 28117186492672688862246691)
            ·
              refine ⟨42175779739009033293370037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28117186492672688862246691 42175779739009033293370037)
              ·
                refine ⟨3953979350532096871253441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42175779739009033293370037 3953979350532096871253441)
                ·
                  refine ⟨2965484512899072653440081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3953979350532096871253441 2965484512899072653440081)
                  ·
                    refine ⟨2224113384674304490080061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965484512899072653440081 2224113384674304490080061)
                    ·
                      refine ⟨834042519252864183780023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2224113384674304490080061 834042519252864183780023)
                      ·
                        rfl

theorem cell23_1624292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_1624292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624292 prefixEnd_1624292 := by exact prefixLift 1624292
  have htrace : WordTrace (prefixWord ++ tailWord_1624292) baseStart_1624292 baseEnd_1624292 := by
    simpa [prefixWord, tailWord_1624292, baseEnd_1624292] using wordTrace_append hprefix tailTrace_1624292
  have hstable : (prefixWord ++ tailWord_1624292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624292).length < 2 ^ (prefixWord ++ tailWord_1624292).sum := by decide
  have hdescent : baseEnd_1624292 < baseStart_1624292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624329 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 6]
def baseStart_1624329 : Nat := 118140960795 + 1624329 * 2 ^ 59
def prefixEnd_1624329 : Nat := 4983230072969 + 3 ^ 40 * 1624329 * 2
def baseEnd_1624329 : Nat := 92673502004120059890817

theorem tailTrace_1624329 : CollatzResearch.WordTrace tailWord_1624329 prefixEnd_1624329 92673502004120059890817 := by
  unfold tailWord_1624329
  simp only [CollatzResearch.WordTrace]
  refine ⟨59244145732340921152308041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39496097154893947434872027 59244145732340921152308041)
  ·
    refine ⟨44433109299255690864231031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59244145732340921152308041 44433109299255690864231031)
    ·
      refine ⟨66649663948883536296346547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44433109299255690864231031 66649663948883536296346547)
      ·
        refine ⟨99974495923325304444519821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66649663948883536296346547 99974495923325304444519821)
        ·
          refine ⟨37490435971246989166694933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99974495923325304444519821 37490435971246989166694933)
          ·
            refine ⟨1757364186152202617188825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37490435971246989166694933 1757364186152202617188825)
            ·
              refine ⟨1318023139614151962891619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757364186152202617188825 1318023139614151962891619)
              ·
                refine ⟨1977034709421227944337429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318023139614151962891619 1977034709421227944337429)
                ·
                  refine ⟨92673502004120059890817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1977034709421227944337429 92673502004120059890817)
                  ·
                    rfl

theorem cell23_1624329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 6].length) (baseStart_1624329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624329 prefixEnd_1624329 := by exact prefixLift 1624329
  have htrace : WordTrace (prefixWord ++ tailWord_1624329) baseStart_1624329 baseEnd_1624329 := by
    simpa [prefixWord, tailWord_1624329, baseEnd_1624329] using wordTrace_append hprefix tailTrace_1624329
  have hstable : (prefixWord ++ tailWord_1624329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624329).length < 2 ^ (prefixWord ++ tailWord_1624329).sum := by decide
  have hdescent : baseEnd_1624329 < baseStart_1624329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624375 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1624375 : Nat := 118140960795 + 1624375 * 2 ^ 59
def prefixEnd_1624375 : Nat := 4983230072969 + 3 ^ 40 * 1624375 * 2
def baseEnd_1624375 : Nat := 834085138147187359042141

theorem tailTrace_1624375 : CollatzResearch.WordTrace tailWord_1624375 prefixEnd_1624375 834085138147187359042141 := by
  unfold tailWord_1624375
  simp only [CollatzResearch.WordTrace]
  refine ⟨59245823490174271008482579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39497215660116180672321719 59245823490174271008482579)
  ·
    refine ⟨88868735235261406512723869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59245823490174271008482579 88868735235261406512723869)
    ·
      refine ⟨33325775713223027442271451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88868735235261406512723869 33325775713223027442271451)
      ·
        refine ⟨49988663569834541163407177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33325775713223027442271451 49988663569834541163407177)
        ·
          refine ⟨37491497677375905872555383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49988663569834541163407177 37491497677375905872555383)
          ·
            refine ⟨56237246516063858808833075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37491497677375905872555383 56237246516063858808833075)
            ·
              refine ⟨84355869774095788213249613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56237246516063858808833075 84355869774095788213249613)
              ·
                refine ⟨31633451165285920579968605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84355869774095788213249613 31633451165285920579968605)
                ·
                  refine ⟨11862544186982220217488227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31633451165285920579968605 11862544186982220217488227)
                  ·
                    refine ⟨17793816280473330326232341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11862544186982220217488227 17793816280473330326232341)
                    ·
                      refine ⟨834085138147187359042141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17793816280473330326232341 834085138147187359042141)
                      ·
                        rfl

theorem cell23_1624375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1624375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624375 prefixEnd_1624375 := by exact prefixLift 1624375
  have htrace : WordTrace (prefixWord ++ tailWord_1624375) baseStart_1624375 baseEnd_1624375 := by
    simpa [prefixWord, tailWord_1624375, baseEnd_1624375] using wordTrace_append hprefix tailTrace_1624375
  have hstable : (prefixWord ++ tailWord_1624375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624375).length < 2 ^ (prefixWord ++ tailWord_1624375).sum := by decide
  have hdescent : baseEnd_1624375 < baseStart_1624375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624392 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1624392 : Nat := 118140960795 + 1624392 * 2 ^ 59
def prefixEnd_1624392 : Nat := 4983230072969 + 3 ^ 40 * 1624392 * 2
def baseEnd_1624392 : Nat := 834093867318313792529563

theorem tailTrace_1624392 : CollatzResearch.WordTrace tailWord_1624392 prefixEnd_1624392 834093867318313792529563 := by
  unfold tailWord_1624392
  simp only [CollatzResearch.WordTrace]
  refine ⟨29623221765556341455925715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39497629020741788607900953 29623221765556341455925715)
  ·
    refine ⟨44434832648334512183888573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29623221765556341455925715 44434832648334512183888573)
    ·
      refine ⟨16663062243125442068958215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44434832648334512183888573 16663062243125442068958215)
      ·
        refine ⟨24994593364688163103437323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16663062243125442068958215 24994593364688163103437323)
        ·
          refine ⟨37491890047032244655155985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24994593364688163103437323 37491890047032244655155985)
          ·
            refine ⟨28118917535274183491366989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37491890047032244655155985 28118917535274183491366989)
            ·
              refine ⟨10544594075727818809262621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28118917535274183491366989 10544594075727818809262621)
              ·
                refine ⟨3954222778397932053473483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10544594075727818809262621 3954222778397932053473483)
                ·
                  refine ⟨5931334167596898080210225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954222778397932053473483 5931334167596898080210225)
                  ·
                    refine ⟨4448500625697673560157669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5931334167596898080210225 4448500625697673560157669)
                    ·
                      refine ⟨834093867318313792529563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4448500625697673560157669 834093867318313792529563)
                      ·
                        rfl

theorem cell23_1624392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1624392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624392 prefixEnd_1624392 := by exact prefixLift 1624392
  have htrace : WordTrace (prefixWord ++ tailWord_1624392) baseStart_1624392 baseEnd_1624392 := by
    simpa [prefixWord, tailWord_1624392, baseEnd_1624392] using wordTrace_append hprefix tailTrace_1624392
  have hstable : (prefixWord ++ tailWord_1624392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624392).length < 2 ^ (prefixWord ++ tailWord_1624392).sum := by decide
  have hdescent : baseEnd_1624392 < baseStart_1624392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624396 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 3, 2, 2]
def baseStart_1624396 : Nat := 118140960795 + 1624396 * 2 ^ 59
def prefixEnd_1624396 : Nat := 4983230072969 + 3 ^ 40 * 1624396 * 2
def baseEnd_1624396 : Nat := 834095921240931776879545

theorem tailTrace_1624396 : CollatzResearch.WordTrace tailWord_1624396 prefixEnd_1624396 834095921240931776879545 := by
  unfold tailWord_1624396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29623294711549095797498521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39497726282065461063331361 29623294711549095797498521)
  ·
    refine ⟨22217471033661821848123891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29623294711549095797498521 22217471033661821848123891)
    ·
      refine ⟨33326206550492732772185837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22217471033661821848123891 33326206550492732772185837)
      ·
        refine ⟨12497327456434774789569689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33326206550492732772185837 12497327456434774789569689)
        ·
          refine ⟨9372995592326081092177267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12497327456434774789569689 9372995592326081092177267)
          ·
            refine ⟨14059493388489121638265901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9372995592326081092177267 14059493388489121638265901)
            ·
              refine ⟨5272310020683420614349713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14059493388489121638265901 5272310020683420614349713)
              ·
                refine ⟨3954232515512565460762285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5272310020683420614349713 3954232515512565460762285)
                ·
                  refine ⟨1482837193317212047785857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3954232515512565460762285 1482837193317212047785857)
                  ·
                    refine ⟨1112127894987909035839393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1482837193317212047785857 1112127894987909035839393)
                    ·
                      refine ⟨834095921240931776879545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112127894987909035839393 834095921240931776879545)
                      ·
                        rfl

theorem cell23_1624396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_1624396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624396 prefixEnd_1624396 := by exact prefixLift 1624396
  have htrace : WordTrace (prefixWord ++ tailWord_1624396) baseStart_1624396 baseEnd_1624396 := by
    simpa [prefixWord, tailWord_1624396, baseEnd_1624396] using wordTrace_append hprefix tailTrace_1624396
  have hstable : (prefixWord ++ tailWord_1624396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624396).length < 2 ^ (prefixWord ++ tailWord_1624396).sum := by decide
  have hdescent : baseEnd_1624396 < baseStart_1624396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624416 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3]
def baseStart_1624416 : Nat := 118140960795 + 1624416 * 2 ^ 59
def prefixEnd_1624416 : Nat := 4983230072969 + 3 ^ 40 * 1624416 * 2
def baseEnd_1624416 : Nat := 834106190854021698629453

theorem tailTrace_1624416 : CollatzResearch.WordTrace tailWord_1624416 prefixEnd_1624416 834106190854021698629453 := by
  unfold tailWord_1624416
  simp only [CollatzResearch.WordTrace]
  refine ⟨29623659441512867505362551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39498212588683823340483401 29623659441512867505362551)
  ·
    refine ⟨44435489162269301258043827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29623659441512867505362551 44435489162269301258043827)
    ·
      refine ⟨66653233743403951887065741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44435489162269301258043827 66653233743403951887065741)
      ·
        refine ⟨24994962653776481957649653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66653233743403951887065741 24994962653776481957649653)
        ·
          refine ⟨2343277748791545183529655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24994962653776481957649653 2343277748791545183529655)
          ·
            refine ⟨3514916623187317775294483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343277748791545183529655 3514916623187317775294483)
            ·
              refine ⟨5272374934780976662941725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514916623187317775294483 5272374934780976662941725)
              ·
                refine ⟨1977140600542866248603147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5272374934780976662941725 1977140600542866248603147)
                ·
                  refine ⟨2965710900814299372904721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977140600542866248603147 2965710900814299372904721)
                  ·
                    refine ⟨2224283175610724529678541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965710900814299372904721 2224283175610724529678541)
                    ·
                      refine ⟨834106190854021698629453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2224283175610724529678541 834106190854021698629453)
                      ·
                        rfl

theorem cell23_1624416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_1624416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624416 prefixEnd_1624416 := by exact prefixLift 1624416
  have htrace : WordTrace (prefixWord ++ tailWord_1624416) baseStart_1624416 baseEnd_1624416 := by
    simpa [prefixWord, tailWord_1624416, baseEnd_1624416] using wordTrace_append hprefix tailTrace_1624416
  have hstable : (prefixWord ++ tailWord_1624416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624416).length < 2 ^ (prefixWord ++ tailWord_1624416).sum := by decide
  have hdescent : baseEnd_1624416 < baseStart_1624416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624439 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 3, 3, 2]
def baseStart_1624439 : Nat := 118140960795 + 1624439 * 2 ^ 59
def prefixEnd_1624439 : Nat := 4983230072969 + 3 ^ 40 * 1624439 * 2
def baseEnd_1624439 : Nat := 834118000909075108641847

theorem tailTrace_1624439 : CollatzResearch.WordTrace tailWord_1624439 prefixEnd_1624439 834118000909075108641847 := by
  unfold tailWord_1624439
  simp only [CollatzResearch.WordTrace]
  refine ⟨59248157761942409938812371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39498771841294939959208247 59248157761942409938812371)
  ·
    refine ⟨88872236642913614908218557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59248157761942409938812371 88872236642913614908218557)
    ·
      refine ⟨33327088741092605590581959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88872236642913614908218557 33327088741092605590581959)
      ·
        refine ⟨49990633111638908385872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33327088741092605590581959 49990633111638908385872939)
        ·
          refine ⟨74985949667458362578809409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49990633111638908385872939 74985949667458362578809409)
          ·
            refine ⟨56239462250593771934107057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74985949667458362578809409 56239462250593771934107057)
            ·
              refine ⟨42179596687945328950580293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56239462250593771934107057 42179596687945328950580293)
              ·
                refine ⟨7908674378989749178233805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42179596687945328950580293 7908674378989749178233805)
                ·
                  refine ⟨2965752892121155941837677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7908674378989749178233805 2965752892121155941837677)
                  ·
                    refine ⟨1112157334545433478189129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2965752892121155941837677 1112157334545433478189129)
                    ·
                      refine ⟨834118000909075108641847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112157334545433478189129 834118000909075108641847)
                      ·
                        rfl

theorem cell23_1624439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_1624439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624439 prefixEnd_1624439 := by exact prefixLift 1624439
  have htrace : WordTrace (prefixWord ++ tailWord_1624439) baseStart_1624439 baseEnd_1624439 := by
    simpa [prefixWord, tailWord_1624439, baseEnd_1624439] using wordTrace_append hprefix tailTrace_1624439
  have hstable : (prefixWord ++ tailWord_1624439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624439).length < 2 ^ (prefixWord ++ tailWord_1624439).sum := by decide
  have hdescent : baseEnd_1624439 < baseStart_1624439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624450 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1624450 : Nat := 118140960795 + 1624450 * 2 ^ 59
def prefixEnd_1624450 : Nat := 4983230072969 + 3 ^ 40 * 1624450 * 2
def baseEnd_1624450 : Nat := 834123649196274565604297

theorem tailTrace_1624450 : CollatzResearch.WordTrace tailWord_1624450 prefixEnd_1624450 834123649196274565604297 := by
  unfold tailWord_1624450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14812139741225639704365701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39499039309935039211641869 14812139741225639704365701)
  ·
    refine ⟨2777276201479807444568569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14812139741225639704365701 2777276201479807444568569)
    ·
      refine ⟨2082957151109855583426427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2777276201479807444568569 2082957151109855583426427)
      ·
        refine ⟨3124435726664783375139641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082957151109855583426427 3124435726664783375139641)
        ·
          refine ⟨2343326794998587531354731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3124435726664783375139641 2343326794998587531354731)
          ·
            refine ⟨3514990192497881297032097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343326794998587531354731 3514990192497881297032097)
            ·
              refine ⟨2636242644373410972774073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514990192497881297032097 2636242644373410972774073)
              ·
                refine ⟨1977181983280058229580555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2636242644373410972774073 1977181983280058229580555)
                ·
                  refine ⟨2965772974920087344370833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977181983280058229580555 2965772974920087344370833)
                  ·
                    refine ⟨2224329731190065508278125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965772974920087344370833 2224329731190065508278125)
                    ·
                      refine ⟨834123649196274565604297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2224329731190065508278125 834123649196274565604297)
                      ·
                        rfl

theorem cell23_1624450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1624450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624450 prefixEnd_1624450 := by exact prefixLift 1624450
  have htrace : WordTrace (prefixWord ++ tailWord_1624450) baseStart_1624450 baseEnd_1624450 := by
    simpa [prefixWord, tailWord_1624450, baseEnd_1624450] using wordTrace_append hprefix tailTrace_1624450
  have hstable : (prefixWord ++ tailWord_1624450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624450).length < 2 ^ (prefixWord ++ tailWord_1624450).sum := by decide
  have hdescent : baseEnd_1624450 < baseStart_1624450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624469 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_1624469 : Nat := 118140960795 + 1624469 * 2 ^ 59
def prefixEnd_1624469 : Nat := 4983230072969 + 3 ^ 40 * 1624469 * 2
def baseEnd_1624469 : Nat := 834133405328709991266709

theorem tailTrace_1624469 : CollatzResearch.WordTrace tailWord_1624469 prefixEnd_1624469 834133405328709991266709 := by
  unfold tailWord_1624469
  simp only [CollatzResearch.WordTrace]
  refine ⟨59249251951833725062404461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39499501301222483374936307 59249251951833725062404461)
  ·
    refine ⟨22218469481937646898401673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59249251951833725062404461 22218469481937646898401673)
    ·
      refine ⟨16663852111453235173801255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22218469481937646898401673 16663852111453235173801255)
      ·
        refine ⟨24995778167179852760701883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16663852111453235173801255 24995778167179852760701883)
        ·
          refine ⟨37493667250769779141052825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24995778167179852760701883 37493667250769779141052825)
          ·
            refine ⟨28120250438077334355789619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37493667250769779141052825 28120250438077334355789619)
            ·
              refine ⟨42180375657116001533684429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28120250438077334355789619 42180375657116001533684429)
              ·
                refine ⟨15817640871418500575131661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42180375657116001533684429 15817640871418500575131661)
                ·
                  refine ⟨5931615326781937715674373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15817640871418500575131661 5931615326781937715674373)
                  ·
                    refine ⟨1112177873771613321688945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931615326781937715674373 1112177873771613321688945)
                    ·
                      refine ⟨834133405328709991266709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112177873771613321688945 834133405328709991266709)
                      ·
                        rfl

theorem cell23_1624469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_1624469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624469 prefixEnd_1624469 := by exact prefixLift 1624469
  have htrace : WordTrace (prefixWord ++ tailWord_1624469) baseStart_1624469 baseEnd_1624469 := by
    simpa [prefixWord, tailWord_1624469, baseEnd_1624469] using wordTrace_append hprefix tailTrace_1624469
  have hstable : (prefixWord ++ tailWord_1624469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624469).length < 2 ^ (prefixWord ++ tailWord_1624469).sum := by decide
  have hdescent : baseEnd_1624469 < baseStart_1624469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624470 : List Nat := [5, 3, 1, 2, 2, 1, 9]
def baseStart_1624470 : Nat := 118140960795 + 1624470 * 2 ^ 59
def prefixEnd_1624470 : Nat := 4983230072969 + 3 ^ 40 * 1624470 * 2
def baseEnd_1624470 : Nat := 10297949614930425769805

theorem tailTrace_1624470 : CollatzResearch.WordTrace tailWord_1624470 prefixEnd_1624470 10297949614930425769805 := by
  unfold tailWord_1624470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703080526551881389574429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39499525616553401488793909 3703080526551881389574429)
  ·
    refine ⟨1388655197456955521090411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3703080526551881389574429 1388655197456955521090411)
    ·
      refine ⟨2082982796185433281635617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388655197456955521090411 2082982796185433281635617)
      ·
        refine ⟨1562237097139074961226713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2082982796185433281635617 1562237097139074961226713)
        ·
          refine ⟨1171677822854306220920035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562237097139074961226713 1171677822854306220920035)
          ·
            refine ⟨1757516734281459331380053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171677822854306220920035 1757516734281459331380053)
            ·
              refine ⟨10297949614930425769805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1757516734281459331380053 10297949614930425769805)
              ·
                rfl

theorem cell23_1624470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 9].length) (baseStart_1624470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624470 prefixEnd_1624470 := by exact prefixLift 1624470
  have htrace : WordTrace (prefixWord ++ tailWord_1624470) baseStart_1624470 baseEnd_1624470 := by
    simpa [prefixWord, tailWord_1624470, baseEnd_1624470] using wordTrace_append hprefix tailTrace_1624470
  have hstable : (prefixWord ++ tailWord_1624470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624470).length < 2 ^ (prefixWord ++ tailWord_1624470).sum := by decide
  have hdescent : baseEnd_1624470 < baseStart_1624470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624503 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 2, 2, 2]
def baseStart_1624503 : Nat := 118140960795 + 1624503 * 2 ^ 59
def prefixEnd_1624503 : Nat := 4983230072969 + 3 ^ 40 * 1624503 * 2
def baseEnd_1624503 : Nat := 834150863670962858241553

theorem tailTrace_1624503 : CollatzResearch.WordTrace tailWord_1624503 prefixEnd_1624503 834150863670962858241553 := by
  unfold tailWord_1624503
  simp only [CollatzResearch.WordTrace]
  refine ⟨59250492033710548869142163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39500328022473699246094775 59250492033710548869142163)
  ·
    refine ⟨88875738050565823303713245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59250492033710548869142163 88875738050565823303713245)
    ·
      refine ⟨33328401768962183738892467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88875738050565823303713245 33328401768962183738892467)
      ·
        refine ⟨49992602653443275608338701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33328401768962183738892467 49992602653443275608338701)
        ·
          refine ⟨18747225995041228353127013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49992602653443275608338701 18747225995041228353127013)
          ·
            refine ⟨3515104874070230316211315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18747225995041228353127013 3515104874070230316211315)
            ·
              refine ⟨5272657311105345474316973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515104874070230316211315 5272657311105345474316973)
              ·
                refine ⟨1977246491664504552868865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5272657311105345474316973 1977246491664504552868865)
                ·
                  refine ⟨1482934868748378414651649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1977246491664504552868865 1482934868748378414651649)
                  ·
                    refine ⟨1112201151561283810988737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1482934868748378414651649 1112201151561283810988737)
                    ·
                      refine ⟨834150863670962858241553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112201151561283810988737 834150863670962858241553)
                      ·
                        rfl

theorem cell23_1624503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_1624503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624503 prefixEnd_1624503 := by exact prefixLift 1624503
  have htrace : WordTrace (prefixWord ++ tailWord_1624503) baseStart_1624503 baseEnd_1624503 := by
    simpa [prefixWord, tailWord_1624503, baseEnd_1624503] using wordTrace_append hprefix tailTrace_1624503
  have hstable : (prefixWord ++ tailWord_1624503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624503).length < 2 ^ (prefixWord ++ tailWord_1624503).sum := by decide
  have hdescent : baseEnd_1624503 < baseStart_1624503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624529 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 4, 5, 2]
def baseStart_1624529 : Nat := 118140960795 + 1624529 * 2 ^ 59
def prefixEnd_1624529 : Nat := 4983230072969 + 3 ^ 40 * 1624529 * 2
def baseEnd_1624529 : Nat := 834164214167979756516433

theorem tailTrace_1624529 : CollatzResearch.WordTrace tailWord_1624529 prefixEnd_1624529 834164214167979756516433 := by
  unfold tailWord_1624529
  simp only [CollatzResearch.WordTrace]
  refine ⟨59251440331616355309588641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39500960221077570206392427 59251440331616355309588641)
  ·
    refine ⟨44438580248712266482191481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59251440331616355309588641 44438580248712266482191481)
    ·
      refine ⟨33328935186534199861643611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44438580248712266482191481 33328935186534199861643611)
      ·
        refine ⟨49993402779801299792465417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33328935186534199861643611 49993402779801299792465417)
        ·
          refine ⟨37495052084850974844349063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49993402779801299792465417 37495052084850974844349063)
          ·
            refine ⟨56242578127276462266523595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37495052084850974844349063 56242578127276462266523595)
            ·
              refine ⟨84363867190914693399785393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56242578127276462266523595 84363867190914693399785393)
              ·
                refine ⟨63272900393186020049839045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84363867190914693399785393 63272900393186020049839045)
                ·
                  refine ⟨11863668823722378759344821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63272900393186020049839045 11863668823722378759344821)
                  ·
                    refine ⟨1112218952223973008688577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11863668823722378759344821 1112218952223973008688577)
                    ·
                      refine ⟨834164214167979756516433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112218952223973008688577 834164214167979756516433)
                      ·
                        rfl

theorem cell23_1624529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_1624529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624529 prefixEnd_1624529 := by exact prefixLift 1624529
  have htrace : WordTrace (prefixWord ++ tailWord_1624529) baseStart_1624529 baseEnd_1624529 := by
    simpa [prefixWord, tailWord_1624529, baseEnd_1624529] using wordTrace_append hprefix tailTrace_1624529
  have hstable : (prefixWord ++ tailWord_1624529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624529).length < 2 ^ (prefixWord ++ tailWord_1624529).sum := by decide
  have hdescent : baseEnd_1624529 < baseStart_1624529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624543 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 5]
def baseStart_1624543 : Nat := 118140960795 + 1624543 * 2 ^ 59
def prefixEnd_1624543 : Nat := 4983230072969 + 3 ^ 40 * 1624543 * 2
def baseEnd_1624543 : Nat := 92685711433015855749041

theorem tailTrace_1624543 : CollatzResearch.WordTrace tailWord_1624543 prefixEnd_1624543 92685711433015855749041 := by
  unfold tailWord_1624543
  simp only [CollatzResearch.WordTrace]
  refine ⟨59251950953565635700598283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39501300635710423800398855 59251950953565635700598283)
  ·
    refine ⟨88877926430348453550897425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59251950953565635700598283 88877926430348453550897425)
    ·
      refine ⟨66658444822761340163173069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88877926430348453550897425 66658444822761340163173069)
      ·
        refine ⟨24996916808535502561189901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66658444822761340163173069 24996916808535502561189901)
        ·
          refine ⟨9373843803200813460446213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24996916808535502561189901 9373843803200813460446213)
          ·
            refine ⟨1757595713100152523833665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9373843803200813460446213 1757595713100152523833665)
            ·
              refine ⟨1318196784825114392875249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757595713100152523833665 1318196784825114392875249)
              ·
                refine ⟨988647588618835794656437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318196784825114392875249 988647588618835794656437)
                ·
                  refine ⟨92685711433015855749041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 988647588618835794656437 92685711433015855749041)
                  ·
                    rfl

theorem cell23_1624543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 5].length) (baseStart_1624543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624543 prefixEnd_1624543 := by exact prefixLift 1624543
  have htrace : WordTrace (prefixWord ++ tailWord_1624543) baseStart_1624543 baseEnd_1624543 := by
    simpa [prefixWord, tailWord_1624543, baseEnd_1624543] using wordTrace_append hprefix tailTrace_1624543
  have hstable : (prefixWord ++ tailWord_1624543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624543).length < 2 ^ (prefixWord ++ tailWord_1624543).sum := by decide
  have hdescent : baseEnd_1624543 < baseStart_1624543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624569 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 5, 4]
def baseStart_1624569 : Nat := 118140960795 + 1624569 * 2 ^ 59
def prefixEnd_1624569 : Nat := 4983230072969 + 3 ^ 40 * 1624569 * 2
def baseEnd_1624569 : Nat := 278061584464719866672083

theorem tailTrace_1624569 : CollatzResearch.WordTrace tailWord_1624569 prefixEnd_1624569 278061584464719866672083 := by
  unfold tailWord_1624569
  simp only [CollatzResearch.WordTrace]
  refine ⟨59252899251471442141044761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39501932834314294760696507 59252899251471442141044761)
  ·
    refine ⟨44439674438603581605783571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59252899251471442141044761 44439674438603581605783571)
    ·
      refine ⟨66659511657905372408675357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44439674438603581605783571 66659511657905372408675357)
      ·
        refine ⟨24997316871714514653253259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66659511657905372408675357 24997316871714514653253259)
        ·
          refine ⟨37495975307571771979879889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24997316871714514653253259 37495975307571771979879889)
          ·
            refine ⟨28121981480678828984909917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37495975307571771979879889 28121981480678828984909917)
            ·
              refine ⟨10545743055254560869341219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28121981480678828984909917 10545743055254560869341219)
              ·
                refine ⟨15818614582881841304011829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10545743055254560869341219 15818614582881841304011829)
                ·
                  refine ⟨1482995117145172622251109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15818614582881841304011829 1482995117145172622251109)
                  ·
                    refine ⟨278061584464719866672083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1482995117145172622251109 278061584464719866672083)
                    ·
                      rfl

theorem cell23_1624569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_1624569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624569 prefixEnd_1624569 := by exact prefixLift 1624569
  have htrace : WordTrace (prefixWord ++ tailWord_1624569) baseStart_1624569 baseEnd_1624569 := by
    simpa [prefixWord, tailWord_1624569, baseEnd_1624569] using wordTrace_append hprefix tailTrace_1624569
  have hstable : (prefixWord ++ tailWord_1624569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624569).length < 2 ^ (prefixWord ++ tailWord_1624569).sum := by decide
  have hdescent : baseEnd_1624569 < baseStart_1624569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624579 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 3]
def baseStart_1624579 : Nat := 118140960795 + 1624579 * 2 ^ 59
def prefixEnd_1624579 : Nat := 4983230072969 + 3 ^ 40 * 1624579 * 2
def baseEnd_1624579 : Nat := 834189888200704560891203

theorem tailTrace_1624579 : CollatzResearch.WordTrace tailWord_1624579 prefixEnd_1624579 834189888200704560891203 := by
  unfold tailWord_1624579
  simp only [CollatzResearch.WordTrace]
  refine ⟨59253263981435213848908791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39502175987623475899272527 59253263981435213848908791)
  ·
    refine ⟨88879895972152820773363187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59253263981435213848908791 88879895972152820773363187)
    ·
      refine ⟨133319843958229231160044781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88879895972152820773363187 133319843958229231160044781)
      ·
        refine ⟨49994941484335961685016793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133319843958229231160044781 49994941484335961685016793)
        ·
          refine ⟨37496206113251971263762595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49994941484335961685016793 37496206113251971263762595)
          ·
            refine ⟨56244309169877956895643893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37496206113251971263762595 56244309169877956895643893)
            ·
              refine ⟨5272903984676058458966615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56244309169877956895643893 5272903984676058458966615)
              ·
                refine ⟨7909355977014087688449923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272903984676058458966615 7909355977014087688449923)
                ·
                  refine ⟨11864033965521131532674885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7909355977014087688449923 11864033965521131532674885)
                  ·
                    refine ⟨2224506368535212162376541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11864033965521131532674885 2224506368535212162376541)
                    ·
                      refine ⟨834189888200704560891203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2224506368535212162376541 834189888200704560891203)
                      ·
                        rfl

theorem cell23_1624579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_1624579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624579 prefixEnd_1624579 := by exact prefixLift 1624579
  have htrace : WordTrace (prefixWord ++ tailWord_1624579) baseStart_1624579 baseEnd_1624579 := by
    simpa [prefixWord, tailWord_1624579, baseEnd_1624579] using wordTrace_append hprefix tailTrace_1624579
  have hstable : (prefixWord ++ tailWord_1624579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624579).length < 2 ^ (prefixWord ++ tailWord_1624579).sum := by decide
  have hdescent : baseEnd_1624579 < baseStart_1624579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624649 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_1624649 : Nat := 118140960795 + 1624649 * 2 ^ 59
def prefixEnd_1624649 : Nat := 4983230072969 + 3 ^ 40 * 1624649 * 2
def baseEnd_1624649 : Nat := 834225831846519287015881

theorem tailTrace_1624649 : CollatzResearch.WordTrace tailWord_1624649 prefixEnd_1624649 834225831846519287015881 := by
  unfold tailWord_1624649
  simp only [CollatzResearch.WordTrace]
  refine ⟨59255817091181615803957001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39503878060787743869304667 59255817091181615803957001)
  ·
    refine ⟨44441862818386211852967751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59255817091181615803957001 44441862818386211852967751)
    ·
      refine ⟨66662794227579317779451627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44441862818386211852967751 66662794227579317779451627)
      ·
        refine ⟨99994191341368976669177441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66662794227579317779451627 99994191341368976669177441)
        ·
          refine ⟨74995643506026732501883081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99994191341368976669177441 74995643506026732501883081)
          ·
            refine ⟨56246732629520049376412311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74995643506026732501883081 56246732629520049376412311)
            ·
              refine ⟨84370098944280074064618467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56246732629520049376412311 84370098944280074064618467)
              ·
                refine ⟨126555148416420111096927701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84370098944280074064618467 126555148416420111096927701)
                ·
                  refine ⟨2966136291009846353834243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126555148416420111096927701 2966136291009846353834243)
                  ·
                    refine ⟨4449204436514769530751365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2966136291009846353834243 4449204436514769530751365)
                    ·
                      refine ⟨834225831846519287015881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4449204436514769530751365 834225831846519287015881)
                      ·
                        rfl

theorem cell23_1624649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_1624649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624649 prefixEnd_1624649 := by exact prefixLift 1624649
  have htrace : WordTrace (prefixWord ++ tailWord_1624649) baseStart_1624649 baseEnd_1624649 := by
    simpa [prefixWord, tailWord_1624649, baseEnd_1624649] using wordTrace_append hprefix tailTrace_1624649
  have hstable : (prefixWord ++ tailWord_1624649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624649).length < 2 ^ (prefixWord ++ tailWord_1624649).sum := by decide
  have hdescent : baseEnd_1624649 < baseStart_1624649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624660 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1624660 : Nat := 118140960795 + 1624660 * 2 ^ 59
def prefixEnd_1624660 : Nat := 4983230072969 + 3 ^ 40 * 1624660 * 2
def baseEnd_1624660 : Nat := 834231480133718743978331

theorem tailTrace_1624660 : CollatzResearch.WordTrace tailWord_1624660 prefixEnd_1624660 834231480133718743978331 := by
  unfold tailWord_1624660
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628109147070882341303717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39504145529427843121738289 29628109147070882341303717)
  ·
    refine ⟨5555270465075790438994447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29628109147070882341303717 5555270465075790438994447)
    ·
      refine ⟨8332905697613685658491671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555270465075790438994447 8332905697613685658491671)
      ·
        refine ⟨12499358546420528487737507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332905697613685658491671 12499358546420528487737507)
        ·
          refine ⟨18749037819630792731606261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12499358546420528487737507 18749037819630792731606261)
          ·
            refine ⟨1757722295590386818588087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18749037819630792731606261 1757722295590386818588087)
            ·
              refine ⟨2636583443385580227882131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757722295590386818588087 2636583443385580227882131)
              ·
                refine ⟨3954875165078370341823197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636583443385580227882131 3954875165078370341823197)
                ·
                  refine ⟨1483078186904388878183699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3954875165078370341823197 1483078186904388878183699)
                  ·
                    refine ⟨2224617280356583317275549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1483078186904388878183699 2224617280356583317275549)
                    ·
                      refine ⟨834231480133718743978331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2224617280356583317275549 834231480133718743978331)
                      ·
                        rfl

theorem cell23_1624660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1624660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624660 prefixEnd_1624660 := by exact prefixLift 1624660
  have htrace : WordTrace (prefixWord ++ tailWord_1624660) baseStart_1624660 baseEnd_1624660 := by
    simpa [prefixWord, tailWord_1624660, baseEnd_1624660] using wordTrace_append hprefix tailTrace_1624660
  have hstable : (prefixWord ++ tailWord_1624660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624660).length < 2 ^ (prefixWord ++ tailWord_1624660).sum := by decide
  have hdescent : baseEnd_1624660 < baseStart_1624660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624680 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1624680 : Nat := 118140960795 + 1624680 * 2 ^ 59
def prefixEnd_1624680 : Nat := 4983230072969 + 3 ^ 40 * 1624680 * 2
def baseEnd_1624680 : Nat := 278080583248936221909413

theorem tailTrace_1624680 : CollatzResearch.WordTrace tailWord_1624680 prefixEnd_1624680 278080583248936221909413 := by
  unfold tailWord_1624680
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628473877034654049167747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39504631836046205398890329 29628473877034654049167747)
  ·
    refine ⟨44442710815551981073751621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29628473877034654049167747 44442710815551981073751621)
    ·
      refine ⟨8333008277915996451328429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44442710815551981073751621 8333008277915996451328429)
      ·
        refine ⟨3124878104218498669248161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8333008277915996451328429 3124878104218498669248161)
        ·
          refine ⟨2343658578163874001936121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3124878104218498669248161 2343658578163874001936121)
          ·
            refine ⟨1757743933622905501452091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343658578163874001936121 1757743933622905501452091)
            ·
              refine ⟨2636615900434358252178137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757743933622905501452091 2636615900434358252178137)
              ·
                refine ⟨1977461925325768689133603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2636615900434358252178137 1977461925325768689133603)
                ·
                  refine ⟨2966192887988653033700405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977461925325768689133603 2966192887988653033700405)
                  ·
                    refine ⟨278080583248936221909413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2966192887988653033700405 278080583248936221909413)
                    ·
                      rfl

theorem cell23_1624680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1624680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624680 prefixEnd_1624680 := by exact prefixLift 1624680
  have htrace : WordTrace (prefixWord ++ tailWord_1624680) baseStart_1624680 baseEnd_1624680 := by
    simpa [prefixWord, tailWord_1624680, baseEnd_1624680] using wordTrace_append hprefix tailTrace_1624680
  have hstable : (prefixWord ++ tailWord_1624680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624680).length < 2 ^ (prefixWord ++ tailWord_1624680).sum := by decide
  have hdescent : baseEnd_1624680 < baseStart_1624680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624693 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1624693 : Nat := 118140960795 + 1624693 * 2 ^ 59
def prefixEnd_1624693 : Nat := 4983230072969 + 3 ^ 40 * 1624693 * 2
def baseEnd_1624693 : Nat := 278082808331772371621893

theorem tailTrace_1624693 : CollatzResearch.WordTrace tailWord_1624693 prefixEnd_1624693 278082808331772371621893 := by
  unfold tailWord_1624693
  simp only [CollatzResearch.WordTrace]
  refine ⟨59257421903022211318558733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39504947935348140879039155 59257421903022211318558733)
  ·
    refine ⟨22221533213633329244459525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59257421903022211318558733 22221533213633329244459525)
    ·
      refine ⟨4166537477556249233336161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22221533213633329244459525 4166537477556249233336161)
      ·
        refine ⟨3124903108167186925002121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4166537477556249233336161 3124903108167186925002121)
        ·
          refine ⟨2343677331125390193751591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3124903108167186925002121 2343677331125390193751591)
          ·
            refine ⟨3515515996688085290627387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343677331125390193751591 3515515996688085290627387)
            ·
              refine ⟨5273273995032127935941081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515515996688085290627387 5273273995032127935941081)
              ·
                refine ⟨3954955496274095951955811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273273995032127935941081 3954955496274095951955811)
                ·
                  refine ⟨5932433244411143927933717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954955496274095951955811 5932433244411143927933717)
                  ·
                    refine ⟨278082808331772371621893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5932433244411143927933717 278082808331772371621893)
                    ·
                      rfl

theorem cell23_1624693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1624693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624693 prefixEnd_1624693 := by exact prefixLift 1624693
  have htrace : WordTrace (prefixWord ++ tailWord_1624693) baseStart_1624693 baseEnd_1624693 := by
    simpa [prefixWord, tailWord_1624693, baseEnd_1624693] using wordTrace_append hprefix tailTrace_1624693
  have hstable : (prefixWord ++ tailWord_1624693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624693).length < 2 ^ (prefixWord ++ tailWord_1624693).sum := by decide
  have hdescent : baseEnd_1624693 < baseStart_1624693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624730 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1624730 : Nat := 118140960795 + 1624730 * 2 ^ 59
def prefixEnd_1624730 : Nat := 4983230072969 + 3 ^ 40 * 1624730 * 2
def baseEnd_1624730 : Nat := 834267423779533470103009

theorem tailTrace_1624730 : CollatzResearch.WordTrace tailWord_1624730 prefixEnd_1624730 834267423779533470103009 := by
  unfold tailWord_1624730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14814692850972041659413911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39505847602592111091770429 14814692850972041659413911)
  ·
    refine ⟨22222039276458062489120867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14814692850972041659413911 22222039276458062489120867)
    ·
      refine ⟨33333058914687093733681301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22222039276458062489120867 33333058914687093733681301)
      ·
        refine ⟨1562487136625957518766311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33333058914687093733681301 1562487136625957518766311)
        ·
          refine ⟨2343730704938936278149467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562487136625957518766311 2343730704938936278149467)
          ·
            refine ⟨3515596057408404417224201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343730704938936278149467 3515596057408404417224201)
            ·
              refine ⟨2636697043056303312918151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515596057408404417224201 2636697043056303312918151)
              ·
                refine ⟨3955045564584454969377227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636697043056303312918151 3955045564584454969377227)
                ·
                  refine ⟨5932568346876682454065841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955045564584454969377227 5932568346876682454065841)
                  ·
                    refine ⟨4449426260157511840549381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5932568346876682454065841 4449426260157511840549381)
                    ·
                      refine ⟨834267423779533470103009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4449426260157511840549381 834267423779533470103009)
                      ·
                        rfl

theorem cell23_1624730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1624730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624730 prefixEnd_1624730 := by exact prefixLift 1624730
  have htrace : WordTrace (prefixWord ++ tailWord_1624730) baseStart_1624730 baseEnd_1624730 := by
    simpa [prefixWord, tailWord_1624730, baseEnd_1624730] using wordTrace_append hprefix tailTrace_1624730
  have hstable : (prefixWord ++ tailWord_1624730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624730).length < 2 ^ (prefixWord ++ tailWord_1624730).sum := by decide
  have hdescent : baseEnd_1624730 < baseStart_1624730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624750 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1624750 : Nat := 118140960795 + 1624750 * 2 ^ 59
def prefixEnd_1624750 : Nat := 4983230072969 + 3 ^ 40 * 1624750 * 2
def baseEnd_1624750 : Nat := 834277693392623391852917

theorem tailTrace_1624750 : CollatzResearch.WordTrace tailWord_1624750 prefixEnd_1624750 834277693392623391852917 := by
  unfold tailWord_1624750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407437607976963756672963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39506333909210473368922469 7407437607976963756672963)
  ·
    refine ⟨11111156411965445635009445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7407437607976963756672963 11111156411965445635009445)
    ·
      refine ⟨2083341827243521056564271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11111156411965445635009445 2083341827243521056564271)
      ·
        refine ⟨3125012740865281584846407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083341827243521056564271 3125012740865281584846407)
        ·
          refine ⟨4687519111297922377269611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125012740865281584846407 4687519111297922377269611)
          ·
            refine ⟨7031278666946883565904417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687519111297922377269611 7031278666946883565904417)
            ·
              refine ⟨5273459000210162674428313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7031278666946883565904417 5273459000210162674428313)
              ·
                refine ⟨3955094250157622005821235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273459000210162674428313 3955094250157622005821235)
                ·
                  refine ⟨5932641375236433008731853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955094250157622005821235 5932641375236433008731853)
                  ·
                    refine ⟨2224740515713662378274445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5932641375236433008731853 2224740515713662378274445)
                    ·
                      refine ⟨834277693392623391852917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2224740515713662378274445 834277693392623391852917)
                      ·
                        rfl

theorem cell23_1624750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1624750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624750 prefixEnd_1624750 := by exact prefixLift 1624750
  have htrace : WordTrace (prefixWord ++ tailWord_1624750) baseStart_1624750 baseEnd_1624750 := by
    simpa [prefixWord, tailWord_1624750, baseEnd_1624750] using wordTrace_append hprefix tailTrace_1624750
  have hstable : (prefixWord ++ tailWord_1624750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624750).length < 2 ^ (prefixWord ++ tailWord_1624750).sum := by decide
  have hdescent : baseEnd_1624750 < baseStart_1624750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624766 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1624766 : Nat := 118140960795 + 1624766 * 2 ^ 59
def prefixEnd_1624766 : Nat := 4983230072969 + 3 ^ 40 * 1624766 * 2
def baseEnd_1624766 : Nat := 278095303027698443084281

theorem tailTrace_1624766 : CollatzResearch.WordTrace tailWord_1624766 prefixEnd_1624766 278095303027698443084281 := by
  unfold tailWord_1624766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407510553969718098245769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39506722954505163190644101 7407510553969718098245769)
  ·
    refine ⟨5555632915477288573684327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7407510553969718098245769 5555632915477288573684327)
    ·
      refine ⟨8333449373215932860526491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555632915477288573684327 8333449373215932860526491)
      ·
        refine ⟨12500174059823899290789737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333449373215932860526491 12500174059823899290789737)
        ·
          refine ⟨9375130544867924468092303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12500174059823899290789737 9375130544867924468092303)
          ·
            refine ⟨14062695817301886702138455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375130544867924468092303 14062695817301886702138455)
            ·
              refine ⟨21094043725952830053207683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14062695817301886702138455 21094043725952830053207683)
              ·
                refine ⟨31641065588929245079811525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21094043725952830053207683 31641065588929245079811525)
                ·
                  refine ⟨5932699797924233452464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31641065588929245079811525 5932699797924233452464661)
                  ·
                    refine ⟨278095303027698443084281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5932699797924233452464661 278095303027698443084281)
                    ·
                      rfl

theorem cell23_1624766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1624766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624766 prefixEnd_1624766 := by exact prefixLift 1624766
  have htrace : WordTrace (prefixWord ++ tailWord_1624766) baseStart_1624766 baseEnd_1624766 := by
    simpa [prefixWord, tailWord_1624766, baseEnd_1624766] using wordTrace_append hprefix tailTrace_1624766
  have hstable : (prefixWord ++ tailWord_1624766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624766).length < 2 ^ (prefixWord ++ tailWord_1624766).sum := by decide
  have hdescent : baseEnd_1624766 < baseStart_1624766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624826 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_1624826 : Nat := 118140960795 + 1624826 * 2 ^ 59
def prefixEnd_1624826 : Nat := 4983230072969 + 3 ^ 40 * 1624826 * 2
def baseEnd_1624826 : Nat := 278105572640788364834189

theorem tailTrace_1624826 : CollatzResearch.WordTrace tailWord_1624826 prefixEnd_1624826 278105572640788364834189 := by
  unfold tailWord_1624826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815568202885093758287583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39508181874360250022100221 14815568202885093758287583)
  ·
    refine ⟨22223352304327640637431375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14815568202885093758287583 22223352304327640637431375)
    ·
      refine ⟨33335028456491460956147063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22223352304327640637431375 33335028456491460956147063)
      ·
        refine ⟨50002542684737191434220595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33335028456491460956147063 50002542684737191434220595)
        ·
          refine ⟨75003814027105787151330893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50002542684737191434220595 75003814027105787151330893)
          ·
            refine ⟨28126430260164670181749085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75003814027105787151330893 28126430260164670181749085)
            ·
              refine ⟨10547411347561751318155907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28126430260164670181749085 10547411347561751318155907)
              ·
                refine ⟨15821117021342626977233861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547411347561751318155907 15821117021342626977233861)
                ·
                  refine ⟨2966459441501742558231349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15821117021342626977233861 2966459441501742558231349)
                  ·
                    refine ⟨278105572640788364834189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2966459441501742558231349 278105572640788364834189)
                    ·
                      rfl

theorem cell23_1624826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_1624826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624826 prefixEnd_1624826 := by exact prefixLift 1624826
  have htrace : WordTrace (prefixWord ++ tailWord_1624826) baseStart_1624826 baseEnd_1624826 := by
    simpa [prefixWord, tailWord_1624826, baseEnd_1624826] using wordTrace_append hprefix tailTrace_1624826
  have hstable : (prefixWord ++ tailWord_1624826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624826).length < 2 ^ (prefixWord ++ tailWord_1624826).sum := by decide
  have hdescent : baseEnd_1624826 < baseStart_1624826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624830 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_1624830 : Nat := 118140960795 + 1624830 * 2 ^ 59
def prefixEnd_1624830 : Nat := 4983230072969 + 3 ^ 40 * 1624830 * 2
def baseEnd_1624830 : Nat := 92702085760553675428061

theorem tailTrace_1624830 : CollatzResearch.WordTrace tailWord_1624830 prefixEnd_1624830 92702085760553675428061 := by
  unfold tailWord_1624830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407802337940735464536993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39508279135683922477530629 7407802337940735464536993)
  ·
    refine ⟨5555851753455551598402745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7407802337940735464536993 5555851753455551598402745)
    ·
      refine ⟨4166888815091663698802059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5555851753455551598402745 4166888815091663698802059)
      ·
        refine ⟨6250333222637495548203089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166888815091663698802059 6250333222637495548203089)
        ·
          refine ⟨4687749916978121661152317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6250333222637495548203089 4687749916978121661152317)
          ·
            refine ⟨1757906218866795622932119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4687749916978121661152317 1757906218866795622932119)
            ·
              refine ⟨2636859328300193434398179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757906218866795622932119 2636859328300193434398179)
              ·
                refine ⟨3955288992450290151597269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636859328300193434398179 3955288992450290151597269)
                ·
                  refine ⟨92702085760553675428061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3955288992450290151597269 92702085760553675428061)
                  ·
                    rfl

theorem cell23_1624830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_1624830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624830 prefixEnd_1624830 := by exact prefixLift 1624830
  have htrace : WordTrace (prefixWord ++ tailWord_1624830) baseStart_1624830 baseEnd_1624830 := by
    simpa [prefixWord, tailWord_1624830, baseEnd_1624830] using wordTrace_append hprefix tailTrace_1624830
  have hstable : (prefixWord ++ tailWord_1624830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624830).length < 2 ^ (prefixWord ++ tailWord_1624830).sum := by decide
  have hdescent : baseEnd_1624830 < baseStart_1624830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624833 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_1624833 : Nat := 118140960795 + 1624833 * 2 ^ 59
def prefixEnd_1624833 : Nat := 4983230072969 + 3 ^ 40 * 1624833 * 2
def baseEnd_1624833 : Nat := 834320312286946567115035

theorem tailTrace_1624833 : CollatzResearch.WordTrace tailWord_1624833 prefixEnd_1624833 834320312286946567115035 := by
  unfold tailWord_1624833
  simp only [CollatzResearch.WordTrace]
  refine ⟨59262528122515015228655153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39508352081676676819103435 59262528122515015228655153)
  ·
    refine ⟨44446896091886261421491365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59262528122515015228655153 44446896091886261421491365)
    ·
      refine ⟨8333793017228674016529631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44446896091886261421491365 8333793017228674016529631)
      ·
        refine ⟨12500689525843011024794447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333793017228674016529631 12500689525843011024794447)
        ·
          refine ⟨18751034288764516537191671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12500689525843011024794447 18751034288764516537191671)
          ·
            refine ⟨28126551433146774805787507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18751034288764516537191671 28126551433146774805787507)
            ·
              refine ⟨42189827149720162208681261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28126551433146774805787507 42189827149720162208681261)
              ·
                refine ⟨15821185181145060828255473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42189827149720162208681261 15821185181145060828255473)
                ·
                  refine ⟨11865888885858795621191605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15821185181145060828255473 11865888885858795621191605)
                  ·
                    refine ⟨1112427083049262089486713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11865888885858795621191605 1112427083049262089486713)
                    ·
                      refine ⟨834320312286946567115035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112427083049262089486713 834320312286946567115035)
                      ·
                        rfl

theorem cell23_1624833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_1624833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624833 prefixEnd_1624833 := by exact prefixLift 1624833
  have htrace : WordTrace (prefixWord ++ tailWord_1624833) baseStart_1624833 baseEnd_1624833 := by
    simpa [prefixWord, tailWord_1624833, baseEnd_1624833] using wordTrace_append hprefix tailTrace_1624833
  have hstable : (prefixWord ++ tailWord_1624833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624833).length < 2 ^ (prefixWord ++ tailWord_1624833).sum := by decide
  have hdescent : baseEnd_1624833 < baseStart_1624833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624863 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1624863 : Nat := 118140960795 + 1624863 * 2 ^ 59
def prefixEnd_1624863 : Nat := 4983230072969 + 3 ^ 40 * 1624863 * 2
def baseEnd_1624863 : Nat := 834335716706581449739897

theorem tailTrace_1624863 : CollatzResearch.WordTrace tailWord_1624863 prefixEnd_1624863 834335716706581449739897 := by
  unfold tailWord_1624863
  simp only [CollatzResearch.WordTrace]
  refine ⟨59263622312406330352247243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39509081541604220234831495 59263622312406330352247243)
  ·
    refine ⟨88895433468609495528370865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59263622312406330352247243 88895433468609495528370865)
    ·
      refine ⟨66671575101457121646278149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88895433468609495528370865 66671575101457121646278149)
      ·
        refine ⟨12500920331523210308677153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66671575101457121646278149 12500920331523210308677153)
        ·
          refine ⟨9375690248642407731507865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12500920331523210308677153 9375690248642407731507865)
          ·
            refine ⟨7031767686481805798630899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375690248642407731507865 7031767686481805798630899)
            ·
              refine ⟨10547651529722708697946349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031767686481805798630899 10547651529722708697946349)
              ·
                refine ⟨3955369323646015761729881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10547651529722708697946349 3955369323646015761729881)
                ·
                  refine ⟨2966526992734511821297411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3955369323646015761729881 2966526992734511821297411)
                  ·
                    refine ⟨4449790489101767731946117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2966526992734511821297411 4449790489101767731946117)
                    ·
                      refine ⟨834335716706581449739897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4449790489101767731946117 834335716706581449739897)
                      ·
                        rfl

theorem cell23_1624863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1624863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624863 prefixEnd_1624863 := by exact prefixLift 1624863
  have htrace : WordTrace (prefixWord ++ tailWord_1624863) baseStart_1624863 baseEnd_1624863 := by
    simpa [prefixWord, tailWord_1624863, baseEnd_1624863] using wordTrace_append hprefix tailTrace_1624863
  have hstable : (prefixWord ++ tailWord_1624863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624863).length < 2 ^ (prefixWord ++ tailWord_1624863).sum := by decide
  have hdescent : baseEnd_1624863 < baseStart_1624863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624876 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1624876 : Nat := 118140960795 + 1624876 * 2 ^ 59
def prefixEnd_1624876 : Nat := 4983230072969 + 3 ^ 40 * 1624876 * 2
def baseEnd_1624876 : Nat := 834342391955089898877337

theorem tailTrace_1624876 : CollatzResearch.WordTrace tailWord_1624876 prefixEnd_1624876 834342391955089898877337 := by
  unfold tailWord_1624876
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632048230679616786235241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39509397640906155714980321 29632048230679616786235241)
  ·
    refine ⟨22224036173009712589676431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29632048230679616786235241 22224036173009712589676431)
    ·
      refine ⟨33336054259514568884514647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22224036173009712589676431 33336054259514568884514647)
      ·
        refine ⟨50004081389271853326771971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33336054259514568884514647 50004081389271853326771971)
        ·
          refine ⟨75006122083907779990157957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50004081389271853326771971 75006122083907779990157957)
          ·
            refine ⟨14063647890732708748154617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75006122083907779990157957 14063647890732708748154617)
            ·
              refine ⟨10547735918049531561115963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14063647890732708748154617 10547735918049531561115963)
              ·
                refine ⟨15821603877074297341673945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547735918049531561115963 15821603877074297341673945)
                ·
                  refine ⟨11866202907805723006255459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15821603877074297341673945 11866202907805723006255459)
                  ·
                    refine ⟨17799304361708584509383189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11866202907805723006255459 17799304361708584509383189)
                    ·
                      refine ⟨834342391955089898877337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17799304361708584509383189 834342391955089898877337)
                      ·
                        rfl

theorem cell23_1624876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1624876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624876 prefixEnd_1624876 := by exact prefixLift 1624876
  have htrace : WordTrace (prefixWord ++ tailWord_1624876) baseStart_1624876 baseEnd_1624876 := by
    simpa [prefixWord, tailWord_1624876, baseEnd_1624876] using wordTrace_append hprefix tailTrace_1624876
  have hstable : (prefixWord ++ tailWord_1624876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624876).length < 2 ^ (prefixWord ++ tailWord_1624876).sum := by decide
  have hdescent : baseEnd_1624876 < baseStart_1624876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624906 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1624906 : Nat := 118140960795 + 1624906 * 2 ^ 59
def prefixEnd_1624906 : Nat := 4983230072969 + 3 ^ 40 * 1624906 * 2
def baseEnd_1624906 : Nat := 834357796374724781502199

theorem tailTrace_1624906 : CollatzResearch.WordTrace tailWord_1624906 prefixEnd_1624906 834357796374724781502199 := by
  unfold tailWord_1624906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14816297662812637174015643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39510127100833699130708381 14816297662812637174015643)
  ·
    refine ⟨22224446494218955761023465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14816297662812637174015643 22224446494218955761023465)
    ·
      refine ⟨16668334870664216820767599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22224446494218955761023465 16668334870664216820767599)
      ·
        refine ⟨25002502305996325231151399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16668334870664216820767599 25002502305996325231151399)
        ·
          refine ⟨37503753458994487846727099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25002502305996325231151399 37503753458994487846727099)
          ·
            refine ⟨56255630188491731770090649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37503753458994487846727099 56255630188491731770090649)
            ·
              refine ⟨42191722641368798827567987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56255630188491731770090649 42191722641368798827567987)
              ·
                refine ⟨63287583962053198241351981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42191722641368798827567987 63287583962053198241351981)
                ·
                  refine ⟨23732843985769949340506993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63287583962053198241351981 23732843985769949340506993)
                  ·
                    refine ⟨17799632989327462005380245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23732843985769949340506993 17799632989327462005380245)
                    ·
                      refine ⟨834357796374724781502199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17799632989327462005380245 834357796374724781502199)
                      ·
                        rfl

theorem cell23_1624906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1624906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624906 prefixEnd_1624906 := by exact prefixLift 1624906
  have htrace : WordTrace (prefixWord ++ tailWord_1624906) baseStart_1624906 baseEnd_1624906 := by
    simpa [prefixWord, tailWord_1624906, baseEnd_1624906] using wordTrace_append hprefix tailTrace_1624906
  have hstable : (prefixWord ++ tailWord_1624906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624906).length < 2 ^ (prefixWord ++ tailWord_1624906).sum := by decide
  have hdescent : baseEnd_1624906 < baseStart_1624906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624924 : List Nat := [2, 2, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1624924 : Nat := 118140960795 + 1624924 * 2 ^ 59
def prefixEnd_1624924 : Nat := 4983230072969 + 3 ^ 40 * 1624924 * 2
def baseEnd_1624924 : Nat := 278122346342168570359039

theorem tailTrace_1624924 : CollatzResearch.WordTrace tailWord_1624924 prefixEnd_1624924 278122346342168570359039 := by
  unfold tailWord_1624924
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632923582592668885108913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39510564776790225180145217 29632923582592668885108913)
  ·
    refine ⟨22224692686944501663831685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29632923582592668885108913 22224692686944501663831685)
    ·
      refine ⟨4167129878802094061968441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22224692686944501663831685 4167129878802094061968441)
      ·
        refine ⟨3125347409101570546476331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4167129878802094061968441 3125347409101570546476331)
        ·
          refine ⟨4688021113652355819714497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125347409101570546476331 4688021113652355819714497)
          ·
            refine ⟨3516015835239266864785873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688021113652355819714497 3516015835239266864785873)
            ·
              refine ⟨2637011876429450148589405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516015835239266864785873 2637011876429450148589405)
              ·
                refine ⟨988879453661043805721027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2637011876429450148589405 988879453661043805721027)
                ·
                  refine ⟨1483319180491565708581541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988879453661043805721027 1483319180491565708581541)
                  ·
                    refine ⟨278122346342168570359039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1483319180491565708581541 278122346342168570359039)
                    ·
                      rfl

theorem cell23_1624924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1624924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624924 prefixEnd_1624924 := by exact prefixLift 1624924
  have htrace : WordTrace (prefixWord ++ tailWord_1624924) baseStart_1624924 baseEnd_1624924 := by
    simpa [prefixWord, tailWord_1624924, baseEnd_1624924] using wordTrace_append hprefix tailTrace_1624924
  have hstable : (prefixWord ++ tailWord_1624924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624924).length < 2 ^ (prefixWord ++ tailWord_1624924).sum := by decide
  have hdescent : baseEnd_1624924 < baseStart_1624924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624940 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 4, 3, 2]
def baseStart_1624940 : Nat := 118140960795 + 1624940 * 2 ^ 59
def prefixEnd_1624940 : Nat := 4983230072969 + 3 ^ 40 * 1624940 * 2
def baseEnd_1624940 : Nat := 834375254716977648477043

theorem tailTrace_1624940 : CollatzResearch.WordTrace tailWord_1624940 prefixEnd_1624940 834375254716977648477043 := by
  unfold tailWord_1624940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29633215366563686251400137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39510953822084915001866849 29633215366563686251400137)
  ·
    refine ⟨22224911524922764688550103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29633215366563686251400137 22224911524922764688550103)
    ·
      refine ⟨33337367287384147032825155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22224911524922764688550103 33337367287384147032825155)
      ·
        refine ⟨50006050931076220549237733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33337367287384147032825155 50006050931076220549237733)
        ·
          refine ⟨9376134549576791352982075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50006050931076220549237733 9376134549576791352982075)
          ·
            refine ⟨14064201824365187029473113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9376134549576791352982075 14064201824365187029473113)
            ·
              refine ⟨10548151368273890272104835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14064201824365187029473113 10548151368273890272104835)
              ·
                refine ⟨15822227052410835408157253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10548151368273890272104835 15822227052410835408157253)
                ·
                  refine ⟨2966667572327031639029485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15822227052410835408157253 2966667572327031639029485)
                  ·
                    refine ⟨1112500339622636864636057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2966667572327031639029485 1112500339622636864636057)
                    ·
                      refine ⟨834375254716977648477043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112500339622636864636057 834375254716977648477043)
                      ·
                        rfl

theorem cell23_1624940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_1624940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624940 prefixEnd_1624940 := by exact prefixLift 1624940
  have htrace : WordTrace (prefixWord ++ tailWord_1624940) baseStart_1624940 baseEnd_1624940 := by
    simpa [prefixWord, tailWord_1624940, baseEnd_1624940] using wordTrace_append hprefix tailTrace_1624940
  have hstable : (prefixWord ++ tailWord_1624940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624940).length < 2 ^ (prefixWord ++ tailWord_1624940).sum := by decide
  have hdescent : baseEnd_1624940 < baseStart_1624940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624947 : List Nat := [1, 1, 1, 2, 2, 1, 6, 4, 1, 1, 3]
def baseStart_1624947 : Nat := 118140960795 + 1624947 * 2 ^ 59
def prefixEnd_1624947 : Nat := 4983230072969 + 3 ^ 40 * 1624947 * 2
def baseEnd_1624947 : Nat := 834378849081559121089511

theorem tailTrace_1624947 : CollatzResearch.WordTrace tailWord_1624947 prefixEnd_1624947 834378849081559121089511 := by
  unfold tailWord_1624947
  simp only [CollatzResearch.WordTrace]
  refine ⟨59266686044102012698305095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39511124029401341798870063 59266686044102012698305095)
  ·
    refine ⟨88900029066153019047457643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59266686044102012698305095 88900029066153019047457643)
    ·
      refine ⟨133350043599229528571186465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88900029066153019047457643 133350043599229528571186465)
      ·
        refine ⟨100012532699422146428389849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133350043599229528571186465 100012532699422146428389849)
        ·
          refine ⟨75009399524566609821292387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100012532699422146428389849 75009399524566609821292387)
          ·
            refine ⟨112514099286849914731938581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75009399524566609821292387 112514099286849914731938581)
            ·
              refine ⟨5274098404071089753059621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112514099286849914731938581 5274098404071089753059621)
              ·
                refine ⟨988893450763329328698679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5274098404071089753059621 988893450763329328698679)
                ·
                  refine ⟨1483340176144993993048019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988893450763329328698679 1483340176144993993048019)
                  ·
                    refine ⟨2225010264217490989572029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1483340176144993993048019 2225010264217490989572029)
                    ·
                      refine ⟨834378849081559121089511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2225010264217490989572029 834378849081559121089511)
                      ·
                        rfl

theorem cell23_1624947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 4, 1, 1, 3].length) (baseStart_1624947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624947 prefixEnd_1624947 := by exact prefixLift 1624947
  have htrace : WordTrace (prefixWord ++ tailWord_1624947) baseStart_1624947 baseEnd_1624947 := by
    simpa [prefixWord, tailWord_1624947, baseEnd_1624947] using wordTrace_append hprefix tailTrace_1624947
  have hstable : (prefixWord ++ tailWord_1624947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624947).length < 2 ^ (prefixWord ++ tailWord_1624947).sum := by decide
  have hdescent : baseEnd_1624947 < baseStart_1624947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624980 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1624980 : Nat := 118140960795 + 1624980 * 2 ^ 59
def prefixEnd_1624980 : Nat := 4983230072969 + 3 ^ 40 * 1624980 * 2
def baseEnd_1624980 : Nat := 278131931314385830658953

theorem tailTrace_1624980 : CollatzResearch.WordTrace tailWord_1624980 prefixEnd_1624980 278131931314385830658953 := by
  unfold tailWord_1624980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29633944826491229667128197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39511926435321639556170929 29633944826491229667128197)
  ·
    refine ⟨5556364654967105562586537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29633944826491229667128197 5556364654967105562586537)
    ·
      refine ⟨4167273491225329171939903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5556364654967105562586537 4167273491225329171939903)
      ·
        refine ⟨6250910236837993757909855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167273491225329171939903 6250910236837993757909855)
        ·
          refine ⟨9376365355256990636864783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250910236837993757909855 9376365355256990636864783)
          ·
            refine ⟨14064548032885485955297175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9376365355256990636864783 14064548032885485955297175)
            ·
              refine ⟨21096822049328228932945763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14064548032885485955297175 21096822049328228932945763)
              ·
                refine ⟨31645233073992343399418645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21096822049328228932945763 31645233073992343399418645)
                ·
                  refine ⟨1483370300343391096847749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31645233073992343399418645 1483370300343391096847749)
                  ·
                    refine ⟨278131931314385830658953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1483370300343391096847749 278131931314385830658953)
                    ·
                      rfl

theorem cell23_1624980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1624980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624980 prefixEnd_1624980 := by exact prefixLift 1624980
  have htrace : WordTrace (prefixWord ++ tailWord_1624980) baseStart_1624980 baseEnd_1624980 := by
    simpa [prefixWord, tailWord_1624980, baseEnd_1624980] using wordTrace_append hprefix tailTrace_1624980
  have hstable : (prefixWord ++ tailWord_1624980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624980).length < 2 ^ (prefixWord ++ tailWord_1624980).sum := by decide
  have hdescent : baseEnd_1624980 < baseStart_1624980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624983 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1624983 : Nat := 118140960795 + 1624983 * 2 ^ 59
def prefixEnd_1624983 : Nat := 4983230072969 + 3 ^ 40 * 1624983 * 2
def baseEnd_1624983 : Nat := 834397334385120980239345

theorem tailTrace_1624983 : CollatzResearch.WordTrace tailWord_1624983 prefixEnd_1624983 834397334385120980239345 := by
  unfold tailWord_1624983
  simp only [CollatzResearch.WordTrace]
  refine ⟨59267999071971590846615603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39511999381314393897743735 59267999071971590846615603)
  ·
    refine ⟨88901998607957386269923405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59267999071971590846615603 88901998607957386269923405)
    ·
      refine ⟨33338249477984019851221277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88901998607957386269923405 33338249477984019851221277)
      ·
        refine ⟨12501843554244007444207979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33338249477984019851221277 12501843554244007444207979)
        ·
          refine ⟨18752765331366011166311969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12501843554244007444207979 18752765331366011166311969)
          ·
            refine ⟨14064573998524508374733977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18752765331366011166311969 14064573998524508374733977)
            ·
              refine ⟨10548430498893381281050483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14064573998524508374733977 10548430498893381281050483)
              ·
                refine ⟨15822645748340071921575725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10548430498893381281050483 15822645748340071921575725)
                ·
                  refine ⟨5933492155627526970590897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15822645748340071921575725 5933492155627526970590897)
                  ·
                    refine ⟨4450119116720645227943173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5933492155627526970590897 4450119116720645227943173)
                    ·
                      refine ⟨834397334385120980239345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4450119116720645227943173 834397334385120980239345)
                      ·
                        rfl

theorem cell23_1624983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1624983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624983 prefixEnd_1624983 := by exact prefixLift 1624983
  have htrace : WordTrace (prefixWord ++ tailWord_1624983) baseStart_1624983 baseEnd_1624983 := by
    simpa [prefixWord, tailWord_1624983, baseEnd_1624983] using wordTrace_append hprefix tailTrace_1624983
  have hstable : (prefixWord ++ tailWord_1624983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624983).length < 2 ^ (prefixWord ++ tailWord_1624983).sum := by decide
  have hdescent : baseEnd_1624983 < baseStart_1624983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624993 : List Nat := [1, 2, 3, 4, 1, 1, 11]
def baseStart_1624993 : Nat := 118140960795 + 1624993 * 2 ^ 59
def prefixEnd_1624993 : Nat := 4983230072969 + 3 ^ 40 * 1624993 * 2
def baseEnd_1624993 : Nat := 10301265051748962235979

theorem tailTrace_1624993 : CollatzResearch.WordTrace tailWord_1624993 prefixEnd_1624993 10301265051748962235979 := by
  unfold tailWord_1624993
  simp only [CollatzResearch.WordTrace]
  refine ⟨59268363801935362554479633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39512242534623575036319755 59268363801935362554479633)
  ·
    refine ⟨44451272851451521915859725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59268363801935362554479633 44451272851451521915859725)
    ·
      refine ⟨16669227319294320718447397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44451272851451521915859725 16669227319294320718447397)
      ·
        refine ⟨3125480122367685134708887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16669227319294320718447397 3125480122367685134708887)
        ·
          refine ⟨4688220183551527702063331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125480122367685134708887 4688220183551527702063331)
          ·
            refine ⟨7032330275327291553094997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688220183551527702063331 7032330275327291553094997)
            ·
              refine ⟨10301265051748962235979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7032330275327291553094997 10301265051748962235979)
              ·
                rfl

theorem cell23_1624993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 11].length) (baseStart_1624993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1624993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1624993 prefixEnd_1624993 := by exact prefixLift 1624993
  have htrace : WordTrace (prefixWord ++ tailWord_1624993) baseStart_1624993 baseEnd_1624993 := by
    simpa [prefixWord, tailWord_1624993, baseEnd_1624993] using wordTrace_append hprefix tailTrace_1624993
  have hstable : (prefixWord ++ tailWord_1624993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624993).length < 2 ^ (prefixWord ++ tailWord_1624993).sum := by decide
  have hdescent : baseEnd_1624993 < baseStart_1624993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 3]
def baseStart_1625003 : Nat := 118140960795 + 1625003 * 2 ^ 59
def prefixEnd_1625003 : Nat := 4983230072969 + 3 ^ 40 * 1625003 * 2
def baseEnd_1625003 : Nat := 834407603998210901989253

theorem tailTrace_1625003 : CollatzResearch.WordTrace tailWord_1625003 prefixEnd_1625003 834407603998210901989253 := by
  unfold tailWord_1625003
  simp only [CollatzResearch.WordTrace]
  refine ⟨59268728531899134262343663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39512485687932756174895775 59268728531899134262343663)
  ·
    refine ⟨88903092797848701393515495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59268728531899134262343663 88903092797848701393515495)
    ·
      refine ⟨133354639196773052090273243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88903092797848701393515495 133354639196773052090273243)
      ·
        refine ⟨200031958795159578135409865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133354639196773052090273243 200031958795159578135409865)
        ·
          refine ⟨150023969096369683601557399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200031958795159578135409865 150023969096369683601557399)
          ·
            refine ⟨225035953644554525402336099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150023969096369683601557399 225035953644554525402336099)
            ·
              refine ⟨337553930466831788103504149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225035953644554525402336099 337553930466831788103504149)
              ·
                refine ⟨15822840490632740067351757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 337553930466831788103504149 15822840490632740067351757)
                ·
                  refine ⟨5933565183987277525256909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15822840490632740067351757 5933565183987277525256909)
                  ·
                    refine ⟨2225086943995229071971341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5933565183987277525256909 2225086943995229071971341)
                    ·
                      refine ⟨834407603998210901989253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2225086943995229071971341 834407603998210901989253)
                      ·
                        rfl

theorem cell23_1625003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 3].length) (baseStart_1625003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625003 prefixEnd_1625003 := by exact prefixLift 1625003
  have htrace : WordTrace (prefixWord ++ tailWord_1625003) baseStart_1625003 baseEnd_1625003 := by
    simpa [prefixWord, tailWord_1625003, baseEnd_1625003] using wordTrace_append hprefix tailTrace_1625003
  have hstable : (prefixWord ++ tailWord_1625003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625003).length < 2 ^ (prefixWord ++ tailWord_1625003).sum := by decide
  have hdescent : baseEnd_1625003 < baseStart_1625003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625013 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1625013 : Nat := 118140960795 + 1625013 * 2 ^ 59
def prefixEnd_1625013 : Nat := 4983230072969 + 3 ^ 40 * 1625013 * 2
def baseEnd_1625013 : Nat := 834412738804755862864207

theorem tailTrace_1625013 : CollatzResearch.WordTrace tailWord_1625013 prefixEnd_1625013 834412738804755862864207 := by
  unfold tailWord_1625013
  simp only [CollatzResearch.WordTrace]
  refine ⟨59269093261862905970207693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39512728841241937313471795 59269093261862905970207693)
  ·
    refine ⟨22225909973198589738827885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59269093261862905970207693 22225909973198589738827885)
    ·
      refine ⟨8334716239949471152060457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22225909973198589738827885 8334716239949471152060457)
      ·
        refine ⟨6251037179962103364045343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8334716239949471152060457 6251037179962103364045343)
        ·
          refine ⟨9376555769943155046068015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6251037179962103364045343 9376555769943155046068015)
          ·
            refine ⟨14064833654914732569102023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9376555769943155046068015 14064833654914732569102023)
            ·
              refine ⟨21097250482372098853653035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14064833654914732569102023 21097250482372098853653035)
              ·
                refine ⟨31645875723558148280479553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21097250482372098853653035 31645875723558148280479553)
                ·
                  refine ⟨23734406792668611210359665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31645875723558148280479553 23734406792668611210359665)
                  ·
                    refine ⟨17800805094501458407769749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23734406792668611210359665 17800805094501458407769749)
                    ·
                      refine ⟨834412738804755862864207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17800805094501458407769749 834412738804755862864207)
                      ·
                        rfl

theorem cell23_1625013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1625013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625013 prefixEnd_1625013 := by exact prefixLift 1625013
  have htrace : WordTrace (prefixWord ++ tailWord_1625013) baseStart_1625013 baseEnd_1625013 := by
    simpa [prefixWord, tailWord_1625013, baseEnd_1625013] using wordTrace_append hprefix tailTrace_1625013
  have hstable : (prefixWord ++ tailWord_1625013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625013).length < 2 ^ (prefixWord ++ tailWord_1625013).sum := by decide
  have hdescent : baseEnd_1625013 < baseStart_1625013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625055 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 1, 2, 2]
def baseStart_1625055 : Nat := 118140960795 + 1625055 * 2 ^ 59
def prefixEnd_1625055 : Nat := 4983230072969 + 3 ^ 40 * 1625055 * 2
def baseEnd_1625055 : Nat := 834434304992244698539015

theorem tailTrace_1625055 : CollatzResearch.WordTrace tailWord_1625055 prefixEnd_1625055 834434304992244698539015 := by
  unfold tailWord_1625055
  simp only [CollatzResearch.WordTrace]
  refine ⟨59270625127710747143236619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39513750085140498095491079 59270625127710747143236619)
  ·
    refine ⟨88905937691566120714854929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59270625127710747143236619 88905937691566120714854929)
    ·
      refine ⟨66679453268674590536141197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88905937691566120714854929 66679453268674590536141197)
      ·
        refine ⟨25004794975752971451052949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66679453268674590536141197 25004794975752971451052949)
        ·
          refine ⟨1172099764488420536768107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25004794975752971451052949 1172099764488420536768107)
          ·
            refine ⟨1758149646732630805152161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172099764488420536768107 1758149646732630805152161)
            ·
              refine ⟨1318612235049473103864121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758149646732630805152161 1318612235049473103864121)
              ·
                refine ⟨988959176287104827898091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318612235049473103864121 988959176287104827898091)
                ·
                  refine ⟨1483438764430657241847137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 988959176287104827898091 1483438764430657241847137)
                  ·
                    refine ⟨1112579073322992931385353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1483438764430657241847137 1112579073322992931385353)
                    ·
                      refine ⟨834434304992244698539015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112579073322992931385353 834434304992244698539015)
                      ·
                        rfl

theorem cell23_1625055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_1625055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625055 prefixEnd_1625055 := by exact prefixLift 1625055
  have htrace : WordTrace (prefixWord ++ tailWord_1625055) baseStart_1625055 baseEnd_1625055 := by
    simpa [prefixWord, tailWord_1625055, baseEnd_1625055] using wordTrace_append hprefix tailTrace_1625055
  have hstable : (prefixWord ++ tailWord_1625055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625055).length < 2 ^ (prefixWord ++ tailWord_1625055).sum := by decide
  have hdescent : baseEnd_1625055 < baseStart_1625055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625111 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1625111 : Nat := 118140960795 + 1625111 * 2 ^ 59
def prefixEnd_1625111 : Nat := 4983230072969 + 3 ^ 40 * 1625111 * 2
def baseEnd_1625111 : Nat := 834463059908896479438757

theorem tailTrace_1625111 : CollatzResearch.WordTrace tailWord_1625111 prefixEnd_1625111 834463059908896479438757 := by
  unfold tailWord_1625111
  simp only [CollatzResearch.WordTrace]
  refine ⟨59272667615507868707275187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39515111743671912471516791 59272667615507868707275187)
  ·
    refine ⟨88909001423261803060912781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59272667615507868707275187 88909001423261803060912781)
    ·
      refine ⟨33340875533723176147842293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88909001423261803060912781 33340875533723176147842293)
      ·
        refine ⟨3125707081286547763860215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33340875533723176147842293 3125707081286547763860215)
        ·
          refine ⟨4688560621929821645790323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125707081286547763860215 4688560621929821645790323)
          ·
            refine ⟨7032840932894732468685485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688560621929821645790323 7032840932894732468685485)
            ·
              refine ⟨2637315349835524675757057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7032840932894732468685485 2637315349835524675757057)
              ·
                refine ⟨1977986512376643506817793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637315349835524675757057 1977986512376643506817793)
                ·
                  refine ⟨1483489884282482630113345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1977986512376643506817793 1483489884282482630113345)
                  ·
                    refine ⟨1112617413211861972585009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1483489884282482630113345 1112617413211861972585009)
                    ·
                      refine ⟨834463059908896479438757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112617413211861972585009 834463059908896479438757)
                      ·
                        rfl

theorem cell23_1625111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1625111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625111 prefixEnd_1625111 := by exact prefixLift 1625111
  have htrace : WordTrace (prefixWord ++ tailWord_1625111) baseStart_1625111 baseEnd_1625111 := by
    simpa [prefixWord, tailWord_1625111, baseEnd_1625111] using wordTrace_append hprefix tailTrace_1625111
  have hstable : (prefixWord ++ tailWord_1625111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625111).length < 2 ^ (prefixWord ++ tailWord_1625111).sum := by decide
  have hdescent : baseEnd_1625111 < baseStart_1625111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625117 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 7]
def baseStart_1625117 : Nat := 118140960795 + 1625117 * 2 ^ 59
def prefixEnd_1625117 : Nat := 4983230072969 + 3 ^ 40 * 1625117 * 2
def baseEnd_1625117 : Nat := 92718460088091495107081

theorem tailTrace_1625117 : CollatzResearch.WordTrace tailWord_1625117 prefixEnd_1625117 92718460088091495107081 := by
  unfold tailWord_1625117
  simp only [CollatzResearch.WordTrace]
  refine ⟨59272886453486131731993605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39515257635657421154662403 59272886453486131731993605)
  ·
    refine ⟨11113666210028649699748801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59272886453486131731993605 11113666210028649699748801)
    ·
      refine ⟨8335249657521487274811601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11113666210028649699748801 8335249657521487274811601)
      ·
        refine ⟨6251437243141115456108701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8335249657521487274811601 6251437243141115456108701)
        ·
          refine ⟨2344288966177918296040763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6251437243141115456108701 2344288966177918296040763)
          ·
            refine ⟨3516433449266877444061145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344288966177918296040763 3516433449266877444061145)
            ·
              refine ⟨2637325086950158083045859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516433449266877444061145 2637325086950158083045859)
              ·
                refine ⟨3955987630425237124568789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637325086950158083045859 3955987630425237124568789)
                ·
                  refine ⟨92718460088091495107081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3955987630425237124568789 92718460088091495107081)
                  ·
                    rfl

theorem cell23_1625117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_1625117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625117 prefixEnd_1625117 := by exact prefixLift 1625117
  have htrace : WordTrace (prefixWord ++ tailWord_1625117) baseStart_1625117 baseEnd_1625117 := by
    simpa [prefixWord, tailWord_1625117, baseEnd_1625117] using wordTrace_append hprefix tailTrace_1625117
  have hstable : (prefixWord ++ tailWord_1625117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625117).length < 2 ^ (prefixWord ++ tailWord_1625117).sum := by decide
  have hdescent : baseEnd_1625117 < baseStart_1625117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625143 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 10]
def baseStart_1625143 : Nat := 118140960795 + 1625143 * 2 ^ 59
def prefixEnd_1625143 : Nat := 4983230072969 + 3 ^ 40 * 1625143 * 2
def baseEnd_1625143 : Nat := 278159830429946784746203

theorem tailTrace_1625143 : CollatzResearch.WordTrace tailWord_1625143 prefixEnd_1625143 278159830429946784746203 := by
  unfold tailWord_1625143
  simp only [CollatzResearch.WordTrace]
  refine ⟨59273834751391938172440083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39515889834261292114960055 59273834751391938172440083)
  ·
    refine ⟨88910752127087907258660125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59273834751391938172440083 88910752127087907258660125)
    ·
      refine ⟨33341532047657965221997547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88910752127087907258660125 33341532047657965221997547)
      ·
        refine ⟨50012298071486947832996321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33341532047657965221997547 50012298071486947832996321)
        ·
          refine ⟨37509223553615210874747241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50012298071486947832996321 37509223553615210874747241)
          ·
            refine ⟨28131917665211408156060431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37509223553615210874747241 28131917665211408156060431)
            ·
              refine ⟨42197876497817112234090647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28131917665211408156060431 42197876497817112234090647)
              ·
                refine ⟨63296814746725668351135971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42197876497817112234090647 63296814746725668351135971)
                ·
                  refine ⟨94945222120088502526703957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63296814746725668351135971 94945222120088502526703957)
                  ·
                    refine ⟨278159830429946784746203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 94945222120088502526703957 278159830429946784746203)
                    ·
                      rfl

theorem cell23_1625143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_1625143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625143 prefixEnd_1625143 := by exact prefixLift 1625143
  have htrace : WordTrace (prefixWord ++ tailWord_1625143) baseStart_1625143 baseEnd_1625143 := by
    simpa [prefixWord, tailWord_1625143, baseEnd_1625143] using wordTrace_append hprefix tailTrace_1625143
  have hstable : (prefixWord ++ tailWord_1625143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625143).length < 2 ^ (prefixWord ++ tailWord_1625143).sum := by decide
  have hdescent : baseEnd_1625143 < baseStart_1625143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625224 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 6]
def baseStart_1625224 : Nat := 118140960795 + 1625224 * 2 ^ 59
def prefixEnd_1625224 : Nat := 4983230072969 + 3 ^ 40 * 1625224 * 2
def baseEnd_1625224 : Nat := 92724564802539393036193

theorem tailTrace_1625224 : CollatzResearch.WordTrace tailWord_1625224 prefixEnd_1625224 92724564802539393036193 := by
  unfold tailWord_1625224
  simp only [CollatzResearch.WordTrace]
  refine ⟨29638394532049244503069363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39517859376065659337425817 29638394532049244503069363)
  ·
    refine ⟨44457591798073866754604045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29638394532049244503069363 44457591798073866754604045)
    ·
      refine ⟨16671596924277700032976517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44457591798073866754604045 16671596924277700032976517)
      ·
        refine ⟨3125924423302068756183097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16671596924277700032976517 3125924423302068756183097)
        ·
          refine ⟨2344443317476551567137323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3125924423302068756183097 2344443317476551567137323)
          ·
            refine ⟨3516664976214827350705985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344443317476551567137323 3516664976214827350705985)
            ·
              refine ⟨2637498732161120513029489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516664976214827350705985 2637498732161120513029489)
              ·
                refine ⟨1978124049120840384772117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637498732161120513029489 1978124049120840384772117)
                ·
                  refine ⟨92724564802539393036193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1978124049120840384772117 92724564802539393036193)
                  ·
                    rfl

theorem cell23_1625224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 6].length) (baseStart_1625224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625224 prefixEnd_1625224 := by exact prefixLift 1625224
  have htrace : WordTrace (prefixWord ++ tailWord_1625224) baseStart_1625224 baseEnd_1625224 := by
    simpa [prefixWord, tailWord_1625224, baseEnd_1625224] using wordTrace_append hprefix tailTrace_1625224
  have hstable : (prefixWord ++ tailWord_1625224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625224).length < 2 ^ (prefixWord ++ tailWord_1625224).sum := by decide
  have hdescent : baseEnd_1625224 < baseStart_1625224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625260 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1625260 : Nat := 118140960795 + 1625260 * 2 ^ 59
def prefixEnd_1625260 : Nat := 4983230072969 + 3 ^ 40 * 1625260 * 2
def baseEnd_1625260 : Nat := 834539568526416396475571

theorem tailTrace_1625260 : CollatzResearch.WordTrace tailWord_1625260 prefixEnd_1625260 834539568526416396475571 := by
  unfold tailWord_1625260
  simp only [CollatzResearch.WordTrace]
  refine ⟨29639051045984033577224617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39518734727978711436299489 29639051045984033577224617)
  ·
    refine ⟨22229288284488025182918463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29639051045984033577224617 22229288284488025182918463)
    ·
      refine ⟨33343932426732037774377695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22229288284488025182918463 33343932426732037774377695)
      ·
        refine ⟨50015898640098056661566543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33343932426732037774377695 50015898640098056661566543)
        ·
          refine ⟨75023847960147084992349815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50015898640098056661566543 75023847960147084992349815)
          ·
            refine ⟨112535771940220627488524723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75023847960147084992349815 112535771940220627488524723)
            ·
              refine ⟨168803657910330941232787085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112535771940220627488524723 168803657910330941232787085)
              ·
                refine ⟨63301371716374102962295157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168803657910330941232787085 63301371716374102962295157)
                ·
                  refine ⟨5934503598410072152715171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63301371716374102962295157 5934503598410072152715171)
                  ·
                    refine ⟨8901755397615108229072757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934503598410072152715171 8901755397615108229072757)
                    ·
                      refine ⟨834539568526416396475571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8901755397615108229072757 834539568526416396475571)
                      ·
                        rfl

theorem cell23_1625260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1625260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625260 prefixEnd_1625260 := by exact prefixLift 1625260
  have htrace : WordTrace (prefixWord ++ tailWord_1625260) baseStart_1625260 baseEnd_1625260 := by
    simpa [prefixWord, tailWord_1625260, baseEnd_1625260] using wordTrace_append hprefix tailTrace_1625260
  have hstable : (prefixWord ++ tailWord_1625260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625260).length < 2 ^ (prefixWord ++ tailWord_1625260).sum := by decide
  have hdescent : baseEnd_1625260 < baseStart_1625260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625261 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_1625261 : Nat := 118140960795 + 1625261 * 2 ^ 59
def prefixEnd_1625261 : Nat := 4983230072969 + 3 ^ 40 * 1625261 * 2
def baseEnd_1625261 : Nat := 834540082007070892563067

theorem tailTrace_1625261 : CollatzResearch.WordTrace tailWord_1625261 prefixEnd_1625261 834540082007070892563067 := by
  unfold tailWord_1625261
  simp only [CollatzResearch.WordTrace]
  refine ⟨59278138564964444325235637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39518759043309629550157091 59278138564964444325235637)
  ·
    refine ⟨5557325490465416655490841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59278138564964444325235637 5557325490465416655490841)
    ·
      refine ⟨4167994117849062491618131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5557325490465416655490841 4167994117849062491618131)
      ·
        refine ⟨6251991176773593737427197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167994117849062491618131 6251991176773593737427197)
        ·
          refine ⟨2344496691290097651535199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6251991176773593737427197 2344496691290097651535199)
          ·
            refine ⟨3516745036935146477302799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344496691290097651535199 3516745036935146477302799)
            ·
              refine ⟨5275117555402719715954199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516745036935146477302799 5275117555402719715954199)
              ·
                refine ⟨7912676333104079573931299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275117555402719715954199 7912676333104079573931299)
                ·
                  refine ⟨11869014499656119360896949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912676333104079573931299 11869014499656119360896949)
                  ·
                    refine ⟨1112720109342761190084089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11869014499656119360896949 1112720109342761190084089)
                    ·
                      refine ⟨834540082007070892563067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112720109342761190084089 834540082007070892563067)
                      ·
                        rfl

theorem cell23_1625261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_1625261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625261 prefixEnd_1625261 := by exact prefixLift 1625261
  have htrace : WordTrace (prefixWord ++ tailWord_1625261) baseStart_1625261 baseEnd_1625261 := by
    simpa [prefixWord, tailWord_1625261, baseEnd_1625261] using wordTrace_append hprefix tailTrace_1625261
  have hstable : (prefixWord ++ tailWord_1625261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625261).length < 2 ^ (prefixWord ++ tailWord_1625261).sum := by decide
  have hdescent : baseEnd_1625261 < baseStart_1625261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625274 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2]
def baseStart_1625274 : Nat := 118140960795 + 1625274 * 2 ^ 59
def prefixEnd_1625274 : Nat := 4983230072969 + 3 ^ 40 * 1625274 * 2
def baseEnd_1625274 : Nat := 834546757255579341700507

theorem tailTrace_1625274 : CollatzResearch.WordTrace tailWord_1625274 prefixEnd_1625274 834546757255579341700507 := by
  unfold tailWord_1625274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819653178479336886364719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39519075142611565030305917 14819653178479336886364719)
  ·
    refine ⟨22229479767719005329547079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14819653178479336886364719 22229479767719005329547079)
    ·
      refine ⟨33344219651578507994320619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22229479767719005329547079 33344219651578507994320619)
      ·
        refine ⟨50016329477367761991480929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33344219651578507994320619 50016329477367761991480929)
        ·
          refine ⟨37512247108025821493610697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50016329477367761991480929 37512247108025821493610697)
          ·
            refine ⟨28134185331019366120208023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37512247108025821493610697 28134185331019366120208023)
            ·
              refine ⟨42201277996529049180312035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28134185331019366120208023 42201277996529049180312035)
              ·
                refine ⟨63301916994793573770468053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42201277996529049180312035 63301916994793573770468053)
                ·
                  refine ⟨1483638679565474385245345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63301916994793573770468053 1483638679565474385245345)
                  ·
                    refine ⟨1112729009674105788934009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1483638679565474385245345 1112729009674105788934009)
                    ·
                      refine ⟨834546757255579341700507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112729009674105788934009 834546757255579341700507)
                      ·
                        rfl

theorem cell23_1625274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_1625274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625274 prefixEnd_1625274 := by exact prefixLift 1625274
  have htrace : WordTrace (prefixWord ++ tailWord_1625274) baseStart_1625274 baseEnd_1625274 := by
    simpa [prefixWord, tailWord_1625274, baseEnd_1625274] using wordTrace_append hprefix tailTrace_1625274
  have hstable : (prefixWord ++ tailWord_1625274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625274).length < 2 ^ (prefixWord ++ tailWord_1625274).sum := by decide
  have hdescent : baseEnd_1625274 < baseStart_1625274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625294 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1625294 : Nat := 118140960795 + 1625294 * 2 ^ 59
def prefixEnd_1625294 : Nat := 4983230072969 + 3 ^ 40 * 1625294 * 2
def baseEnd_1625294 : Nat := 834557026868669263450415

theorem tailTrace_1625294 : CollatzResearch.WordTrace tailWord_1625294 prefixEnd_1625294 834557026868669263450415 := by
  unfold tailWord_1625294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7409917771730611370148367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39519561449229927307457957 7409917771730611370148367)
  ·
    refine ⟨11114876657595917055222551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7409917771730611370148367 11114876657595917055222551)
    ·
      refine ⟨16672314986393875582833827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11114876657595917055222551 16672314986393875582833827)
      ·
        refine ⟨25008472479590813374250741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16672314986393875582833827 25008472479590813374250741)
        ·
          refine ⟨2344544294961638753836007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25008472479590813374250741 2344544294961638753836007)
          ·
            refine ⟨3516816442442458130754011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344544294961638753836007 3516816442442458130754011)
            ·
              refine ⟨5275224663663687196131017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516816442442458130754011 5275224663663687196131017)
              ·
                refine ⟨3956418497747765397098263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275224663663687196131017 3956418497747765397098263)
                ·
                  refine ⟨5934627746621648095647395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956418497747765397098263 5934627746621648095647395)
                  ·
                    refine ⟨8901941619932472143471093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934627746621648095647395 8901941619932472143471093)
                    ·
                      refine ⟨834557026868669263450415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8901941619932472143471093 834557026868669263450415)
                      ·
                        rfl

theorem cell23_1625294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1625294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625294 prefixEnd_1625294 := by exact prefixLift 1625294
  have htrace : WordTrace (prefixWord ++ tailWord_1625294) baseStart_1625294 baseEnd_1625294 := by
    simpa [prefixWord, tailWord_1625294, baseEnd_1625294] using wordTrace_append hprefix tailTrace_1625294
  have hstable : (prefixWord ++ tailWord_1625294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625294).length < 2 ^ (prefixWord ++ tailWord_1625294).sum := by decide
  have hdescent : baseEnd_1625294 < baseStart_1625294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625324 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_1625324 : Nat := 118140960795 + 1625324 * 2 ^ 59
def prefixEnd_1625324 : Nat := 4983230072969 + 3 ^ 40 * 1625324 * 2
def baseEnd_1625324 : Nat := 834572431288304146075277

theorem tailTrace_1625324 : CollatzResearch.WordTrace tailWord_1625324 prefixEnd_1625324 834572431288304146075277 := by
  unfold tailWord_1625324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29640218181868103042389513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39520290909157470723186017 29640218181868103042389513)
  ·
    refine ⟨22230163636401077281792135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29640218181868103042389513 22230163636401077281792135)
    ·
      refine ⟨33345245454601615922688203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22230163636401077281792135 33345245454601615922688203)
      ·
        refine ⟨50017868181902423884032305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33345245454601615922688203 50017868181902423884032305)
        ·
          refine ⟨37513401136426817913024229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50017868181902423884032305 37513401136426817913024229)
          ·
            refine ⟨7033762713080028358692043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37513401136426817913024229 7033762713080028358692043)
            ·
              refine ⟨10550644069620042538038065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033762713080028358692043 10550644069620042538038065)
              ·
                refine ⟨7912983052215031903528549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10550644069620042538038065 7912983052215031903528549)
                ·
                  refine ⟨1483684322290318481911603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7912983052215031903528549 1483684322290318481911603)
                  ·
                    refine ⟨2225526483435477722867405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1483684322290318481911603 2225526483435477722867405)
                    ·
                      refine ⟨834572431288304146075277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2225526483435477722867405 834572431288304146075277)
                      ·
                        rfl

theorem cell23_1625324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_1625324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625324 prefixEnd_1625324 := by exact prefixLift 1625324
  have htrace : WordTrace (prefixWord ++ tailWord_1625324) baseStart_1625324 baseEnd_1625324 := by
    simpa [prefixWord, tailWord_1625324, baseEnd_1625324] using wordTrace_append hprefix tailTrace_1625324
  have hstable : (prefixWord ++ tailWord_1625324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625324).length < 2 ^ (prefixWord ++ tailWord_1625324).sum := by decide
  have hdescent : baseEnd_1625324 < baseStart_1625324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625325 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1625325 : Nat := 118140960795 + 1625325 * 2 ^ 59
def prefixEnd_1625325 : Nat := 4983230072969 + 3 ^ 40 * 1625325 * 2
def baseEnd_1625325 : Nat := 834572944768958642162773

theorem tailTrace_1625325 : CollatzResearch.WordTrace tailWord_1625325 prefixEnd_1625325 834572944768958642162773 := by
  unfold tailWord_1625325
  simp only [CollatzResearch.WordTrace]
  refine ⟨59280472836732583255565429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39520315224488388837043619 59280472836732583255565429)
  ·
    refine ⟨5557544328443679680209259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59280472836732583255565429 5557544328443679680209259)
    ·
      refine ⟨8336316492665519520313889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5557544328443679680209259 8336316492665519520313889)
      ·
        refine ⟨6252237369499139640235417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8336316492665519520313889 6252237369499139640235417)
        ·
          refine ⟨4689178027124354730176563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6252237369499139640235417 4689178027124354730176563)
          ·
            refine ⟨7033767040686532095264845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689178027124354730176563 7033767040686532095264845)
            ·
              refine ⟨2637662640257449535724317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7033767040686532095264845 2637662640257449535724317)
              ·
                refine ⟨989123490096543575896619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2637662640257449535724317 989123490096543575896619)
                ·
                  refine ⟨1483685235144815363844929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989123490096543575896619 1483685235144815363844929)
                  ·
                    refine ⟨1112763926358611522883697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1483685235144815363844929 1112763926358611522883697)
                    ·
                      refine ⟨834572944768958642162773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112763926358611522883697 834572944768958642162773)
                      ·
                        rfl

theorem cell23_1625325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1625325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625325 prefixEnd_1625325 := by exact prefixLift 1625325
  have htrace : WordTrace (prefixWord ++ tailWord_1625325) baseStart_1625325 baseEnd_1625325 := by
    simpa [prefixWord, tailWord_1625325, baseEnd_1625325] using wordTrace_append hprefix tailTrace_1625325
  have hstable : (prefixWord ++ tailWord_1625325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625325).length < 2 ^ (prefixWord ++ tailWord_1625325).sum := by decide
  have hdescent : baseEnd_1625325 < baseStart_1625325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625342 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1625342 : Nat := 118140960795 + 1625342 * 2 ^ 59
def prefixEnd_1625342 : Nat := 4983230072969 + 3 ^ 40 * 1625342 * 2
def baseEnd_1625342 : Nat := 834581673940085075650195

theorem tailTrace_1625342 : CollatzResearch.WordTrace tailWord_1625342 prefixEnd_1625342 834581673940085075650195 := by
  unfold tailWord_1625342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410136609708874394866785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39520728585113996772622853 7410136609708874394866785)
  ·
    refine ⟨5557602457281655796150089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7410136609708874394866785 5557602457281655796150089)
    ·
      refine ⟨4168201842961241847112567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5557602457281655796150089 4168201842961241847112567)
      ·
        refine ⟨6252302764441862770668851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168201842961241847112567 6252302764441862770668851)
        ·
          refine ⟨9378454146662794156003277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6252302764441862770668851 9378454146662794156003277)
          ·
            refine ⟨3516920304998547808501229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9378454146662794156003277 3516920304998547808501229)
            ·
              refine ⟨1318845114374455428187961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3516920304998547808501229 1318845114374455428187961)
              ·
                refine ⟨989133835780841571140971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318845114374455428187961 989133835780841571140971)
                ·
                  refine ⟨1483700753671262356711457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989133835780841571140971 1483700753671262356711457)
                  ·
                    refine ⟨1112775565253446767533593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1483700753671262356711457 1112775565253446767533593)
                    ·
                      refine ⟨834581673940085075650195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112775565253446767533593 834581673940085075650195)
                      ·
                        rfl

theorem cell23_1625342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1625342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625342 prefixEnd_1625342 := by exact prefixLift 1625342
  have htrace : WordTrace (prefixWord ++ tailWord_1625342) baseStart_1625342 baseEnd_1625342 := by
    simpa [prefixWord, tailWord_1625342, baseEnd_1625342] using wordTrace_append hprefix tailTrace_1625342
  have hstable : (prefixWord ++ tailWord_1625342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625342).length < 2 ^ (prefixWord ++ tailWord_1625342).sum := by decide
  have hdescent : baseEnd_1625342 < baseStart_1625342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625358 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1625358 : Nat := 118140960795 + 1625358 * 2 ^ 59
def prefixEnd_1625358 : Nat := 4983230072969 + 3 ^ 40 * 1625358 * 2
def baseEnd_1625358 : Nat := 834589889630557013050121

theorem tailTrace_1625358 : CollatzResearch.WordTrace tailWord_1625358 prefixEnd_1625358 834589889630557013050121 := by
  unfold tailWord_1625358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410209555701628736439591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39521117630408686594344485 7410209555701628736439591)
  ·
    refine ⟨11115314333552443104659387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7410209555701628736439591 11115314333552443104659387)
    ·
      refine ⟨16672971500328664656989081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11115314333552443104659387 16672971500328664656989081)
      ·
        refine ⟨12504728625246498492741811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16672971500328664656989081 12504728625246498492741811)
        ·
          refine ⟨18757092937869747739112717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12504728625246498492741811 18757092937869747739112717)
          ·
            refine ⟨7033909851701155402167269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18757092937869747739112717 7033909851701155402167269)
            ·
              refine ⟨1318858097193966637906363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7033909851701155402167269 1318858097193966637906363)
              ·
                refine ⟨1978287145790949956859545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318858097193966637906363 1978287145790949956859545)
                ·
                  refine ⟨1483715359343212467644659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978287145790949956859545 1483715359343212467644659)
                  ·
                    refine ⟨2225573039014818701466989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1483715359343212467644659 2225573039014818701466989)
                    ·
                      refine ⟨834589889630557013050121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2225573039014818701466989 834589889630557013050121)
                      ·
                        rfl

theorem cell23_1625358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1625358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625358 prefixEnd_1625358 := by exact prefixLift 1625358
  have htrace : WordTrace (prefixWord ++ tailWord_1625358) baseStart_1625358 baseEnd_1625358 := by
    simpa [prefixWord, tailWord_1625358, baseEnd_1625358] using wordTrace_append hprefix tailTrace_1625358
  have hstable : (prefixWord ++ tailWord_1625358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625358).length < 2 ^ (prefixWord ++ tailWord_1625358).sum := by decide
  have hdescent : baseEnd_1625358 < baseStart_1625358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625362 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1625362 : Nat := 118140960795 + 1625362 * 2 ^ 59
def prefixEnd_1625362 : Nat := 4983230072969 + 3 ^ 40 * 1625362 * 2
def baseEnd_1625362 : Nat := 834591943553174997400103

theorem tailTrace_1625362 : CollatzResearch.WordTrace tailWord_1625362 prefixEnd_1625362 834591943553174997400103 := by
  unfold tailWord_1625362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14820455584399634643665585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39521214891732359049774893 14820455584399634643665585)
  ·
    refine ⟨11115341688299725982749189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14820455584399634643665585 11115341688299725982749189)
    ·
      refine ⟨2084126566556198621765473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11115341688299725982749189 2084126566556198621765473)
      ·
        refine ⟨1563094924917148966324105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2084126566556198621765473 1563094924917148966324105)
        ·
          refine ⟨1172321193687861724743079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1563094924917148966324105 1172321193687861724743079)
          ·
            refine ⟨1758481790531792587114619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172321193687861724743079 1758481790531792587114619)
            ·
              refine ⟨2637722685797688880671929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758481790531792587114619 2637722685797688880671929)
              ·
                refine ⟨1978292014348266660503947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637722685797688880671929 1978292014348266660503947)
                ·
                  refine ⟨2967438021522399990755921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978292014348266660503947 2967438021522399990755921)
                  ·
                    refine ⟨2225578516141799993066941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2967438021522399990755921 2225578516141799993066941)
                    ·
                      refine ⟨834591943553174997400103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2225578516141799993066941 834591943553174997400103)
                      ·
                        rfl

theorem cell23_1625362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1625362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625362 prefixEnd_1625362 := by exact prefixLift 1625362
  have htrace : WordTrace (prefixWord ++ tailWord_1625362) baseStart_1625362 baseEnd_1625362 := by
    simpa [prefixWord, tailWord_1625362, baseEnd_1625362] using wordTrace_append hprefix tailTrace_1625362
  have hstable : (prefixWord ++ tailWord_1625362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625362).length < 2 ^ (prefixWord ++ tailWord_1625362).sum := by decide
  have hdescent : baseEnd_1625362 < baseStart_1625362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625367 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1625367 : Nat := 118140960795 + 1625367 * 2 ^ 59
def prefixEnd_1625367 : Nat := 4983230072969 + 3 ^ 40 * 1625367 * 2
def baseEnd_1625367 : Nat := 834594510956447477837579

theorem tailTrace_1625367 : CollatzResearch.WordTrace tailWord_1625367 prefixEnd_1625367 834594510956447477837579 := by
  unfold tailWord_1625367
  simp only [CollatzResearch.WordTrace]
  refine ⟨59282004702580424428594355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39521336468386949619062903 59282004702580424428594355)
  ·
    refine ⟨88923007053870636642891533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59282004702580424428594355 88923007053870636642891533)
    ·
      refine ⟨33346127645201488741084325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88923007053870636642891533 33346127645201488741084325)
      ·
        refine ⟨6252398933475279138953311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33346127645201488741084325 6252398933475279138953311)
        ·
          refine ⟨9378598400212918708429967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6252398933475279138953311 9378598400212918708429967)
          ·
            refine ⟨14067897600319378062644951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378598400212918708429967 14067897600319378062644951)
            ·
              refine ⟨21101846400479067093967427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14067897600319378062644951 21101846400479067093967427)
              ·
                refine ⟨31652769600718600640951141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21101846400479067093967427 31652769600718600640951141)
                ·
                  refine ⟨5934894300134737620178339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31652769600718600640951141 5934894300134737620178339)
                  ·
                    refine ⟨8902341450202106430267509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934894300134737620178339 8902341450202106430267509)
                    ·
                      refine ⟨834594510956447477837579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8902341450202106430267509 834594510956447477837579)
                      ·
                        rfl

theorem cell23_1625367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1625367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625367 prefixEnd_1625367 := by exact prefixLift 1625367
  have htrace : WordTrace (prefixWord ++ tailWord_1625367) baseStart_1625367 baseEnd_1625367 := by
    simpa [prefixWord, tailWord_1625367, baseEnd_1625367] using wordTrace_append hprefix tailTrace_1625367
  have hstable : (prefixWord ++ tailWord_1625367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625367).length < 2 ^ (prefixWord ++ tailWord_1625367).sum := by decide
  have hdescent : baseEnd_1625367 < baseStart_1625367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625368 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 1, 3, 2]
def baseStart_1625368 : Nat := 118140960795 + 1625368 * 2 ^ 59
def prefixEnd_1625368 : Nat := 4983230072969 + 3 ^ 40 * 1625368 * 2
def baseEnd_1625368 : Nat := 834595024437101973925075

theorem tailTrace_1625368 : CollatzResearch.WordTrace tailWord_1625368 prefixEnd_1625368 834595024437101973925075 := by
  unfold tailWord_1625368
  simp only [CollatzResearch.WordTrace]
  refine ⟨29641020587788400799690379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39521360783717867732920505 29641020587788400799690379)
  ·
    refine ⟨44461530881682601199535569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29641020587788400799690379 44461530881682601199535569)
    ·
      refine ⟨33346148161261950899651677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44461530881682601199535569 33346148161261950899651677)
      ·
        refine ⟨12504805560473231587369379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33346148161261950899651677 12504805560473231587369379)
        ·
          refine ⟨18757208340709847381054069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12504805560473231587369379 18757208340709847381054069)
          ·
            refine ⟨1758488281941548191973819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18757208340709847381054069 1758488281941548191973819)
            ·
              refine ⟨2637732422912322287960729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758488281941548191973819 2637732422912322287960729)
              ·
                refine ⟨1978299317184241715970547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637732422912322287960729 1978299317184241715970547)
                ·
                  refine ⟨2967448975776362573955821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978299317184241715970547 2967448975776362573955821)
                  ·
                    refine ⟨1112793365916135965233433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967448975776362573955821 1112793365916135965233433)
                    ·
                      refine ⟨834595024437101973925075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112793365916135965233433 834595024437101973925075)
                      ·
                        rfl

theorem cell23_1625368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_1625368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625368 prefixEnd_1625368 := by exact prefixLift 1625368
  have htrace : WordTrace (prefixWord ++ tailWord_1625368) baseStart_1625368 baseEnd_1625368 := by
    simpa [prefixWord, tailWord_1625368, baseEnd_1625368] using wordTrace_append hprefix tailTrace_1625368
  have hstable : (prefixWord ++ tailWord_1625368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625368).length < 2 ^ (prefixWord ++ tailWord_1625368).sum := by decide
  have hdescent : baseEnd_1625368 < baseStart_1625368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625377 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1625377 : Nat := 118140960795 + 1625377 * 2 ^ 59
def prefixEnd_1625377 : Nat := 4983230072969 + 3 ^ 40 * 1625377 * 2
def baseEnd_1625377 : Nat := 834599645762992438712533

theorem tailTrace_1625377 : CollatzResearch.WordTrace tailWord_1625377 prefixEnd_1625377 834599645762992438712533 := by
  unfold tailWord_1625377
  simp only [CollatzResearch.WordTrace]
  refine ⟨59282369432544196136458385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39521579621696130757638923 59282369432544196136458385)
  ·
    refine ⟨44461777074408147102343789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59282369432544196136458385 44461777074408147102343789)
    ·
      refine ⟨16673166402903055163378921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44461777074408147102343789 16673166402903055163378921)
      ·
        refine ⟨12504874802177291372534191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16673166402903055163378921 12504874802177291372534191)
        ·
          refine ⟨18757312203265937058801287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12504874802177291372534191 18757312203265937058801287)
          ·
            refine ⟨28135968304898905588201931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18757312203265937058801287 28135968304898905588201931)
            ·
              refine ⟨42203952457348358382302897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28135968304898905588201931 42203952457348358382302897)
              ·
                refine ⟨31652964343011268786727173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42203952457348358382302897 31652964343011268786727173)
                ·
                  refine ⟨5934930814314612897511345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31652964343011268786727173 5934930814314612897511345)
                  ·
                    refine ⟨4451198110735959673133509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5934930814314612897511345 4451198110735959673133509)
                    ·
                      refine ⟨834599645762992438712533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4451198110735959673133509 834599645762992438712533)
                      ·
                        rfl

theorem cell23_1625377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1625377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625377 prefixEnd_1625377 := by exact prefixLift 1625377
  have htrace : WordTrace (prefixWord ++ tailWord_1625377) baseStart_1625377 baseEnd_1625377 := by
    simpa [prefixWord, tailWord_1625377, baseEnd_1625377] using wordTrace_append hprefix tailTrace_1625377
  have hstable : (prefixWord ++ tailWord_1625377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625377).length < 2 ^ (prefixWord ++ tailWord_1625377).sum := by decide
  have hdescent : baseEnd_1625377 < baseStart_1625377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625381 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 1, 4, 2]
def baseStart_1625381 : Nat := 118140960795 + 1625381 * 2 ^ 59
def prefixEnd_1625381 : Nat := 4983230072969 + 3 ^ 40 * 1625381 * 2
def baseEnd_1625381 : Nat := 834601699685610423062515

theorem tailTrace_1625381 : CollatzResearch.WordTrace tailWord_1625381 prefixEnd_1625381 834601699685610423062515 := by
  unfold tailWord_1625381
  simp only [CollatzResearch.WordTrace]
  refine ⟨59282515324529704819603997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39521676883019803213069331 59282515324529704819603997)
  ·
    refine ⟨22230943246698639307351499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59282515324529704819603997 22230943246698639307351499)
    ·
      refine ⟨33346414870047958961027249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22230943246698639307351499 33346414870047958961027249)
      ·
        refine ⟨25009811152535969220770437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33346414870047958961027249 25009811152535969220770437)
        ·
          refine ⟨4689339591100494228894457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25009811152535969220770437 4689339591100494228894457)
          ·
            refine ⟨3517004693325370671670843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689339591100494228894457 3517004693325370671670843)
            ·
              refine ⟨5275507039988056007506265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517004693325370671670843 5275507039988056007506265)
              ·
                refine ⟨3956630279991042005629699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275507039988056007506265 3956630279991042005629699)
                ·
                  refine ⟨5934945419986563008444549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956630279991042005629699 5934945419986563008444549)
                  ·
                    refine ⟨1112802266247480564083353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5934945419986563008444549 1112802266247480564083353)
                    ·
                      refine ⟨834601699685610423062515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112802266247480564083353 834601699685610423062515)
                      ·
                        rfl

theorem cell23_1625381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_1625381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625381 prefixEnd_1625381 := by exact prefixLift 1625381
  have htrace : WordTrace (prefixWord ++ tailWord_1625381) baseStart_1625381 baseEnd_1625381 := by
    simpa [prefixWord, tailWord_1625381, baseEnd_1625381] using wordTrace_append hprefix tailTrace_1625381
  have hstable : (prefixWord ++ tailWord_1625381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625381).length < 2 ^ (prefixWord ++ tailWord_1625381).sum := by decide
  have hdescent : baseEnd_1625381 < baseStart_1625381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625384 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1625384 : Nat := 118140960795 + 1625384 * 2 ^ 59
def prefixEnd_1625384 : Nat := 4983230072969 + 3 ^ 40 * 1625384 * 2
def baseEnd_1625384 : Nat := 834603240127573911325001

theorem tailTrace_1625384 : CollatzResearch.WordTrace tailWord_1625384 prefixEnd_1625384 834603240127573911325001 := by
  unfold tailWord_1625384
  simp only [CollatzResearch.WordTrace]
  refine ⟨29641312371759418165981603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39521749829012557554642137 29641312371759418165981603)
  ·
    refine ⟨44461968557639127248972405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29641312371759418165981603 44461968557639127248972405)
    ·
      refine ⟨4168309552278668179591163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44461968557639127248972405 4168309552278668179591163)
      ·
        refine ⟨6252464328418002269386745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4168309552278668179591163 6252464328418002269386745)
        ·
          refine ⟨4689348246313501702040059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6252464328418002269386745 4689348246313501702040059)
          ·
            refine ⟨7034022369470252553060089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689348246313501702040059 7034022369470252553060089)
            ·
              refine ⟨5275516777102689414795067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034022369470252553060089 5275516777102689414795067)
              ·
                refine ⟨7913275165654034122192601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275516777102689414795067 7913275165654034122192601)
                ·
                  refine ⟨5934956374240525591644451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913275165654034122192601 5934956374240525591644451)
                  ·
                    refine ⟨8902434561360788387466677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934956374240525591644451 8902434561360788387466677)
                    ·
                      refine ⟨834603240127573911325001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8902434561360788387466677 834603240127573911325001)
                      ·
                        rfl

theorem cell23_1625384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1625384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625384 prefixEnd_1625384 := by exact prefixLift 1625384
  have htrace : WordTrace (prefixWord ++ tailWord_1625384) baseStart_1625384 baseEnd_1625384 := by
    simpa [prefixWord, tailWord_1625384, baseEnd_1625384] using wordTrace_append hprefix tailTrace_1625384
  have hstable : (prefixWord ++ tailWord_1625384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625384).length < 2 ^ (prefixWord ++ tailWord_1625384).sum := by decide
  have hdescent : baseEnd_1625384 < baseStart_1625384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625417 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_1625417 : Nat := 118140960795 + 1625417 * 2 ^ 59
def prefixEnd_1625417 : Nat := 4983230072969 + 3 ^ 40 * 1625417 * 2
def baseEnd_1625417 : Nat := 278206728329724094070783

theorem tailTrace_1625417 : CollatzResearch.WordTrace tailWord_1625417 prefixEnd_1625417 278206728329724094070783 := by
  unfold tailWord_1625417
  simp only [CollatzResearch.WordTrace]
  refine ⟨59283828352399282967914505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39522552234932855311943003 59283828352399282967914505)
  ·
    refine ⟨44462871264299462225935879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59283828352399282967914505 44462871264299462225935879)
    ·
      refine ⟨66694306896449193338903819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44462871264299462225935879 66694306896449193338903819)
      ·
        refine ⟨100041460344673790008355729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66694306896449193338903819 100041460344673790008355729)
        ·
          refine ⟨75031095258505342506266797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100041460344673790008355729 75031095258505342506266797)
          ·
            refine ⟨28136660721939503439850049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75031095258505342506266797 28136660721939503439850049)
            ·
              refine ⟨21102495541454627579887537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28136660721939503439850049 21102495541454627579887537)
              ·
                refine ⟨15826871656090970684915653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21102495541454627579887537 15826871656090970684915653)
                ·
                  refine ⟨2967538435517057003421685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15826871656090970684915653 2967538435517057003421685)
                  ·
                    refine ⟨278206728329724094070783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2967538435517057003421685 278206728329724094070783)
                    ·
                      rfl

theorem cell23_1625417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_1625417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625417 prefixEnd_1625417 := by exact prefixLift 1625417
  have htrace : WordTrace (prefixWord ++ tailWord_1625417) baseStart_1625417 baseEnd_1625417 := by
    simpa [prefixWord, tailWord_1625417, baseEnd_1625417] using wordTrace_append hprefix tailTrace_1625417
  have hstable : (prefixWord ++ tailWord_1625417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625417).length < 2 ^ (prefixWord ++ tailWord_1625417).sum := by decide
  have hdescent : baseEnd_1625417 < baseStart_1625417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625424 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 2, 5, 2]
def baseStart_1625424 : Nat := 118140960795 + 1625424 * 2 ^ 59
def prefixEnd_1625424 : Nat := 4983230072969 + 3 ^ 40 * 1625424 * 2
def baseEnd_1625424 : Nat := 834623779353753754824817

theorem tailTrace_1625424 : CollatzResearch.WordTrace tailWord_1625424 prefixEnd_1625424 834623779353753754824817 := by
  unfold tailWord_1625424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29642041831686961581709663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39522722442249282108946217 29642041831686961581709663)
  ·
    refine ⟨44463062747530442372564495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29642041831686961581709663 44463062747530442372564495)
    ·
      refine ⟨66694594121295663558846743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44463062747530442372564495 66694594121295663558846743)
      ·
        refine ⟨100041891181943495338270115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66694594121295663558846743 100041891181943495338270115)
        ·
          refine ⟨150062836772915243007405173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100041891181943495338270115 150062836772915243007405173)
          ·
            refine ⟨14068390947460804031944235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150062836772915243007405173 14068390947460804031944235)
            ·
              refine ⟨21102586421191206047916353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14068390947460804031944235 21102586421191206047916353)
              ·
                refine ⟨15826939815893404535937265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21102586421191206047916353 15826939815893404535937265)
                ·
                  refine ⟨11870204861920053401952949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15826939815893404535937265 11870204861920053401952949)
                  ·
                    refine ⟨1112831705805005006433089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11870204861920053401952949 1112831705805005006433089)
                    ·
                      refine ⟨834623779353753754824817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112831705805005006433089 834623779353753754824817)
                      ·
                        rfl

theorem cell23_1625424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 2, 5, 2].length) (baseStart_1625424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625424 prefixEnd_1625424 := by exact prefixLift 1625424
  have htrace : WordTrace (prefixWord ++ tailWord_1625424) baseStart_1625424 baseEnd_1625424 := by
    simpa [prefixWord, tailWord_1625424, baseEnd_1625424] using wordTrace_append hprefix tailTrace_1625424
  have hstable : (prefixWord ++ tailWord_1625424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625424).length < 2 ^ (prefixWord ++ tailWord_1625424).sum := by decide
  have hdescent : baseEnd_1625424 < baseStart_1625424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625434 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_1625434 : Nat := 118140960795 + 1625434 * 2 ^ 59
def prefixEnd_1625434 : Nat := 4983230072969 + 3 ^ 40 * 1625434 * 2
def baseEnd_1625434 : Nat := 278209638053432905233257

theorem tailTrace_1625434 : CollatzResearch.WordTrace tailWord_1625434 prefixEnd_1625434 278209638053432905233257 := by
  unfold tailWord_1625434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14821112098334423717820839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39522965595558463247522237 14821112098334423717820839)
  ·
    refine ⟨22231668147501635576731259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14821112098334423717820839 22231668147501635576731259)
    ·
      refine ⟨33347502221252453365096889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22231668147501635576731259 33347502221252453365096889)
      ·
        refine ⟨25010626665939340023822667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33347502221252453365096889 25010626665939340023822667)
        ·
          refine ⟨37515939998909010035734001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25010626665939340023822667 37515939998909010035734001)
          ·
            refine ⟨28136954999181757526800501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37515939998909010035734001 28136954999181757526800501)
            ·
              refine ⟨2637839531173289768137547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28136954999181757526800501 2637839531173289768137547)
              ·
                refine ⟨3956759296759934652206321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637839531173289768137547 3956759296759934652206321)
                ·
                  refine ⟨2967569472569950989154741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3956759296759934652206321 2967569472569950989154741)
                  ·
                    refine ⟨278209638053432905233257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2967569472569950989154741 278209638053432905233257)
                    ·
                      rfl

theorem cell23_1625434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_1625434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625434 prefixEnd_1625434 := by exact prefixLift 1625434
  have htrace : WordTrace (prefixWord ++ tailWord_1625434) baseStart_1625434 baseEnd_1625434 := by
    simpa [prefixWord, tailWord_1625434, baseEnd_1625434] using wordTrace_append hprefix tailTrace_1625434
  have hstable : (prefixWord ++ tailWord_1625434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625434).length < 2 ^ (prefixWord ++ tailWord_1625434).sum := by decide
  have hdescent : baseEnd_1625434 < baseStart_1625434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625457 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_1625457 : Nat := 118140960795 + 1625457 * 2 ^ 59
def prefixEnd_1625457 : Nat := 4983230072969 + 3 ^ 40 * 1625457 * 2
def baseEnd_1625457 : Nat := 834640724215352125712165

theorem tailTrace_1625457 : CollatzResearch.WordTrace tailWord_1625457 prefixEnd_1625457 834640724215352125712165 := by
  unfold tailWord_1625457
  simp only [CollatzResearch.WordTrace]
  refine ⟨59285287272254369799370625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39523524848169579866247083 59285287272254369799370625)
  ·
    refine ⟨44463965454190777349527969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59285287272254369799370625 44463965454190777349527969)
    ·
      refine ⟨33347974090643083012145977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44463965454190777349527969 33347974090643083012145977)
      ·
        refine ⟨25010980567982312259109483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33347974090643083012145977 25010980567982312259109483)
        ·
          refine ⟨37516470851973468388664225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25010980567982312259109483 37516470851973468388664225)
          ·
            refine ⟨28137353138980101291498169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37516470851973468388664225 28137353138980101291498169)
            ·
              refine ⟨21103014854235075968623627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28137353138980101291498169 21103014854235075968623627)
              ·
                refine ⟨31654522281352613952935441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21103014854235075968623627 31654522281352613952935441)
                ·
                  refine ⟨23740891711014460464701581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31654522281352613952935441 23740891711014460464701581)
                  ·
                    refine ⟨8902834391630422674263093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23740891711014460464701581 8902834391630422674263093)
                    ·
                      refine ⟨834640724215352125712165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8902834391630422674263093 834640724215352125712165)
                      ·
                        rfl

theorem cell23_1625457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_1625457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625457 prefixEnd_1625457 := by exact prefixLift 1625457
  have htrace : WordTrace (prefixWord ++ tailWord_1625457) baseStart_1625457 baseEnd_1625457 := by
    simpa [prefixWord, tailWord_1625457, baseEnd_1625457] using wordTrace_append hprefix tailTrace_1625457
  have hstable : (prefixWord ++ tailWord_1625457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625457).length < 2 ^ (prefixWord ++ tailWord_1625457).sum := by decide
  have hdescent : baseEnd_1625457 < baseStart_1625457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625467 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6]
def baseStart_1625467 : Nat := 118140960795 + 1625467 * 2 ^ 59
def prefixEnd_1625467 : Nat := 4983230072969 + 3 ^ 40 * 1625467 * 2
def baseEnd_1625467 : Nat := 834645859021897086587119

theorem tailTrace_1625467 : CollatzResearch.WordTrace tailWord_1625467 prefixEnd_1625467 834645859021897086587119 := by
  unfold tailWord_1625467
  simp only [CollatzResearch.WordTrace]
  refine ⟨59285652002218141507234655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39523768001478761004823103 59285652002218141507234655)
  ·
    refine ⟨88928478003327212260851983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59285652002218141507234655 88928478003327212260851983)
    ·
      refine ⟨133392717004990818391277975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88928478003327212260851983 133392717004990818391277975)
      ·
        refine ⟨200089075507486227586916963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133392717004990818391277975 200089075507486227586916963)
        ·
          refine ⟨300133613261229341380375445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200089075507486227586916963 300133613261229341380375445)
          ·
            refine ⟨14068763121620125377205099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 300133613261229341380375445 14068763121620125377205099)
            ·
              refine ⟨21103144682430188065807649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14068763121620125377205099 21103144682430188065807649)
              ·
                refine ⟨15827358511822641049355737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21103144682430188065807649 15827358511822641049355737)
                ·
                  refine ⟨11870518883866980787016803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15827358511822641049355737 11870518883866980787016803)
                  ·
                    refine ⟨17805778325800471180525205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11870518883866980787016803 17805778325800471180525205)
                    ·
                      refine ⟨834645859021897086587119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17805778325800471180525205 834645859021897086587119)
                      ·
                        rfl

theorem cell23_1625467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_1625467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625467 prefixEnd_1625467 := by exact prefixLift 1625467
  have htrace : WordTrace (prefixWord ++ tailWord_1625467) baseStart_1625467 baseEnd_1625467 := by
    simpa [prefixWord, tailWord_1625467, baseEnd_1625467] using wordTrace_append hprefix tailTrace_1625467
  have hstable : (prefixWord ++ tailWord_1625467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625467).length < 2 ^ (prefixWord ++ tailWord_1625467).sum := by decide
  have hdescent : baseEnd_1625467 < baseStart_1625467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625548 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1625548 : Nat := 118140960795 + 1625548 * 2 ^ 59
def prefixEnd_1625548 : Nat := 4983230072969 + 3 ^ 40 * 1625548 * 2
def baseEnd_1625548 : Nat := 834687450954911269674247

theorem tailTrace_1625548 : CollatzResearch.WordTrace tailWord_1625548 prefixEnd_1625548 834687450954911269674247 := by
  unfold tailWord_1625548
  simp only [CollatzResearch.WordTrace]
  refine ⟨29644303157462346170466649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39525737543283128227288865 29644303157462346170466649)
  ·
    refine ⟨22233227368096759627849987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29644303157462346170466649 22233227368096759627849987)
    ·
      refine ⟨33349841052145139441774981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22233227368096759627849987 33349841052145139441774981)
      ·
        refine ⟨6253095197277213645332809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33349841052145139441774981 6253095197277213645332809)
        ·
          refine ⟨4689821397957910233999607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6253095197277213645332809 4689821397957910233999607)
          ·
            refine ⟨7034732096936865350999411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689821397957910233999607 7034732096936865350999411)
            ·
              refine ⟨10552098145405298026499117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034732096936865350999411 10552098145405298026499117)
              ·
                refine ⟨3957036804526986759937169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10552098145405298026499117 3957036804526986759937169)
                ·
                  refine ⟨2967777603395240069952877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957036804526986759937169 2967777603395240069952877)
                  ·
                    refine ⟨1112916601273215026232329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967777603395240069952877 1112916601273215026232329)
                    ·
                      refine ⟨834687450954911269674247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112916601273215026232329 834687450954911269674247)
                      ·
                        rfl

theorem cell23_1625548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1625548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625548 prefixEnd_1625548 := by exact prefixLift 1625548
  have htrace : WordTrace (prefixWord ++ tailWord_1625548) baseStart_1625548 baseEnd_1625548 := by
    simpa [prefixWord, tailWord_1625548, baseEnd_1625548] using wordTrace_append hprefix tailTrace_1625548
  have hstable : (prefixWord ++ tailWord_1625548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625548).length < 2 ^ (prefixWord ++ tailWord_1625548).sum := by decide
  have hdescent : baseEnd_1625548 < baseStart_1625548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625584 : List Nat := [2, 1, 1, 1, 3, 4, 3, 8]
def baseStart_1625584 : Nat := 118140960795 + 1625584 * 2 ^ 59
def prefixEnd_1625584 : Nat := 4983230072969 + 3 ^ 40 * 1625584 * 2
def baseEnd_1625584 : Nat := 30915034676239745512003

theorem tailTrace_1625584 : CollatzResearch.WordTrace tailWord_1625584 prefixEnd_1625584 30915034676239745512003 := by
  unfold tailWord_1625584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29644959671397135244621903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39526612895196180326162537 29644959671397135244621903)
  ·
    refine ⟨44467439507095702866932855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29644959671397135244621903 44467439507095702866932855)
    ·
      refine ⟨66701159260643554300399283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44467439507095702866932855 66701159260643554300399283)
      ·
        refine ⟨100051738890965331450598925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66701159260643554300399283 100051738890965331450598925)
        ·
          refine ⟨37519402084111999293974597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100051738890965331450598925 37519402084111999293974597)
          ·
            refine ⟨7034887890770999867620237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37519402084111999293974597 7034887890770999867620237)
            ·
              refine ⟨2638082959039124950357589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034887890770999867620237 2638082959039124950357589)
              ·
                refine ⟨30915034676239745512003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2638082959039124950357589 30915034676239745512003)
                ·
                  rfl

theorem cell23_1625584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 8].length) (baseStart_1625584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625584 prefixEnd_1625584 := by exact prefixLift 1625584
  have htrace : WordTrace (prefixWord ++ tailWord_1625584) baseStart_1625584 baseEnd_1625584 := by
    simpa [prefixWord, tailWord_1625584, baseEnd_1625584] using wordTrace_append hprefix tailTrace_1625584
  have hstable : (prefixWord ++ tailWord_1625584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625584).length < 2 ^ (prefixWord ++ tailWord_1625584).sum := by decide
  have hdescent : baseEnd_1625584 < baseStart_1625584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625612 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 1, 1, 4]
def baseStart_1625612 : Nat := 118140960795 + 1625612 * 2 ^ 59
def prefixEnd_1625612 : Nat := 4983230072969 + 3 ^ 40 * 1625612 * 2
def baseEnd_1625612 : Nat := 834720313716799019273953

theorem tailTrace_1625612 : CollatzResearch.WordTrace tailWord_1625612 prefixEnd_1625612 834720313716799019273953 := by
  unfold tailWord_1625612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29645470293346415635631545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39527293724461887514175393 29645470293346415635631545)
  ·
    refine ⟨22234102720009811726723659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29645470293346415635631545 22234102720009811726723659)
    ·
      refine ⟨33351154080014717590085489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22234102720009811726723659 33351154080014717590085489)
      ·
        refine ⟨25013365560011038192564117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33351154080014717590085489 25013365560011038192564117)
        ·
          refine ⟨1172501510625517415276443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25013365560011038192564117 1172501510625517415276443)
          ·
            refine ⟨1758752265938276122914665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172501510625517415276443 1758752265938276122914665)
            ·
              refine ⟨1319064199453707092185999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758752265938276122914665 1319064199453707092185999)
              ·
                refine ⟨1978596299180560638278999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319064199453707092185999 1978596299180560638278999)
                ·
                  refine ⟨2967894448770840957418499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978596299180560638278999 2967894448770840957418499)
                  ·
                    refine ⟨4451841673156261436127749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2967894448770840957418499 4451841673156261436127749)
                    ·
                      refine ⟨834720313716799019273953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4451841673156261436127749 834720313716799019273953)
                      ·
                        rfl

theorem cell23_1625612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_1625612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625612 prefixEnd_1625612 := by exact prefixLift 1625612
  have htrace : WordTrace (prefixWord ++ tailWord_1625612) baseStart_1625612 baseEnd_1625612 := by
    simpa [prefixWord, tailWord_1625612, baseEnd_1625612] using wordTrace_append hprefix tailTrace_1625612
  have hstable : (prefixWord ++ tailWord_1625612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625612).length < 2 ^ (prefixWord ++ tailWord_1625612).sum := by decide
  have hdescent : baseEnd_1625612 < baseStart_1625612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625628 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1625628 : Nat := 118140960795 + 1625628 * 2 ^ 59
def prefixEnd_1625628 : Nat := 4983230072969 + 3 ^ 40 * 1625628 * 2
def baseEnd_1625628 : Nat := 834728529407270956673879

theorem tailTrace_1625628 : CollatzResearch.WordTrace tailWord_1625628 prefixEnd_1625628 834728529407270956673879 := by
  unfold tailWord_1625628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29645762077317433001922769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39527682769756577335897025 29645762077317433001922769)
  ·
    refine ⟨22234321557988074751442077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29645762077317433001922769 22234321557988074751442077)
    ·
      refine ⟨8337870584245528031790779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22234321557988074751442077 8337870584245528031790779)
      ·
        refine ⟨12506805876368292047686169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8337870584245528031790779 12506805876368292047686169)
        ·
          refine ⟨9380104407276219035764627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12506805876368292047686169 9380104407276219035764627)
          ·
            refine ⟨14070156610914328553646941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9380104407276219035764627 14070156610914328553646941)
            ·
              refine ⟨5276308729092873207617603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14070156610914328553646941 5276308729092873207617603)
              ·
                refine ⟨7914463093639309811426405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276308729092873207617603 7914463093639309811426405)
                ·
                  refine ⟨1483961830057370589642451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7914463093639309811426405 1483961830057370589642451)
                  ·
                    refine ⟨2225942745086055884463677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1483961830057370589642451 2225942745086055884463677)
                    ·
                      refine ⟨834728529407270956673879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2225942745086055884463677 834728529407270956673879)
                      ·
                        rfl

theorem cell23_1625628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1625628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625628 prefixEnd_1625628 := by exact prefixLift 1625628
  have htrace : WordTrace (prefixWord ++ tailWord_1625628) baseStart_1625628 baseEnd_1625628 := by
    simpa [prefixWord, tailWord_1625628, baseEnd_1625628] using wordTrace_append hprefix tailTrace_1625628
  have hstable : (prefixWord ++ tailWord_1625628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625628).length < 2 ^ (prefixWord ++ tailWord_1625628).sum := by decide
  have hdescent : baseEnd_1625628 < baseStart_1625628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625655 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 1, 3, 2]
def baseStart_1625655 : Nat := 118140960795 + 1625655 * 2 ^ 59
def prefixEnd_1625655 : Nat := 4983230072969 + 3 ^ 40 * 1625655 * 2
def baseEnd_1625655 : Nat := 834742393384942351036255

theorem tailTrace_1625655 : CollatzResearch.WordTrace tailWord_1625655 prefixEnd_1625655 834742393384942351036255 := by
  unfold tailWord_1625655
  simp only [CollatzResearch.WordTrace]
  refine ⟨59292508925537049615078419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39528339283691366410052279 59292508925537049615078419)
  ·
    refine ⟨88938763388305574422617629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59292508925537049615078419 88938763388305574422617629)
    ·
      refine ⟨33352036270614590408481611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88938763388305574422617629 33352036270614590408481611)
      ·
        refine ⟨50028054405921885612722417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33352036270614590408481611 50028054405921885612722417)
        ·
          refine ⟨37521040804441414209541813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50028054405921885612722417 37521040804441414209541813)
          ·
            refine ⟨3517597575416382582144545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37521040804441414209541813 3517597575416382582144545)
            ·
              refine ⟨2638198181562286936608409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517597575416382582144545 2638198181562286936608409)
              ·
                refine ⟨1978648636171715202456307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638198181562286936608409 1978648636171715202456307)
                ·
                  refine ⟨2967972954257572803684461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978648636171715202456307 2967972954257572803684461)
                  ·
                    refine ⟨1112989857846589801381673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967972954257572803684461 1112989857846589801381673)
                    ·
                      refine ⟨834742393384942351036255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1112989857846589801381673 834742393384942351036255)
                      ·
                        rfl

theorem cell23_1625655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_1625655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625655 prefixEnd_1625655 := by exact prefixLift 1625655
  have htrace : WordTrace (prefixWord ++ tailWord_1625655) baseStart_1625655 baseEnd_1625655 := by
    simpa [prefixWord, tailWord_1625655, baseEnd_1625655] using wordTrace_append hprefix tailTrace_1625655
  have hstable : (prefixWord ++ tailWord_1625655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625655).length < 2 ^ (prefixWord ++ tailWord_1625655).sum := by decide
  have hdescent : baseEnd_1625655 < baseStart_1625655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625685 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_1625685 : Nat := 118140960795 + 1625685 * 2 ^ 59
def prefixEnd_1625685 : Nat := 4983230072969 + 3 ^ 40 * 1625685 * 2
def baseEnd_1625685 : Nat := 834757797804577233661117

theorem tailTrace_1625685 : CollatzResearch.WordTrace tailWord_1625685 prefixEnd_1625685 834757797804577233661117 := by
  unfold tailWord_1625685
  simp only [CollatzResearch.WordTrace]
  refine ⟨59293603115428364738670509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39529068743618909825780339 59293603115428364738670509)
  ·
    refine ⟨22235101168285636777001441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59293603115428364738670509 22235101168285636777001441)
    ·
      refine ⟨16676325876214227582751081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22235101168285636777001441 16676325876214227582751081)
      ·
        refine ⟨12507244407160670687063311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16676325876214227582751081 12507244407160670687063311)
        ·
          refine ⟨18760866610741006030594967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12507244407160670687063311 18760866610741006030594967)
          ·
            refine ⟨28141299916111509045892451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18760866610741006030594967 28141299916111509045892451)
            ·
              refine ⟨42211949874167263568838677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28141299916111509045892451 42211949874167263568838677)
              ·
                refine ⟨1978685150351590479789313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42211949874167263568838677 1978685150351590479789313)
                ·
                  refine ⟨1484013862763692859841985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1978685150351590479789313 1484013862763692859841985)
                  ·
                    refine ⟨1113010397072769644881489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1484013862763692859841985 1113010397072769644881489)
                    ·
                      refine ⟨834757797804577233661117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113010397072769644881489 834757797804577233661117)
                      ·
                        rfl

theorem cell23_1625685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_1625685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625685 prefixEnd_1625685 := by exact prefixLift 1625685
  have htrace : WordTrace (prefixWord ++ tailWord_1625685) baseStart_1625685 baseEnd_1625685 := by
    simpa [prefixWord, tailWord_1625685, baseEnd_1625685] using wordTrace_append hprefix tailTrace_1625685
  have hstable : (prefixWord ++ tailWord_1625685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625685).length < 2 ^ (prefixWord ++ tailWord_1625685).sum := by decide
  have hdescent : baseEnd_1625685 < baseStart_1625685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625738 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1625738 : Nat := 118140960795 + 1625738 * 2 ^ 59
def prefixEnd_1625738 : Nat := 4983230072969 + 3 ^ 40 * 1625738 * 2
def baseEnd_1625738 : Nat := 278261670759755175432791

theorem tailTrace_1625738 : CollatzResearch.WordTrace tailWord_1625738 prefixEnd_1625738 278261670759755175432791 := by
  unfold tailWord_1625738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823884046059088697587467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39530357456157569860233245 14823884046059088697587467)
  ·
    refine ⟨22235826069088633046381201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14823884046059088697587467 22235826069088633046381201)
    ·
      refine ⟨16676869551816474784785901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22235826069088633046381201 16676869551816474784785901)
      ·
        refine ⟨6253826081931178044294713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16676869551816474784785901 6253826081931178044294713)
        ·
          refine ⟨4690369561448383533221035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6253826081931178044294713 4690369561448383533221035)
          ·
            refine ⟨7035554342172575299831553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690369561448383533221035 7035554342172575299831553)
            ·
              refine ⟨5276665756629431474873665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035554342172575299831553 5276665756629431474873665)
              ·
                refine ⟨3957499317472073606155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276665756629431474873665 3957499317472073606155249)
                ·
                  refine ⟨2968124488104055204616437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957499317472073606155249 2968124488104055204616437)
                  ·
                    refine ⟨278261670759755175432791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2968124488104055204616437 278261670759755175432791)
                    ·
                      rfl

theorem cell23_1625738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1625738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625738 prefixEnd_1625738 := by exact prefixLift 1625738
  have htrace : WordTrace (prefixWord ++ tailWord_1625738) baseStart_1625738 baseEnd_1625738 := by
    simpa [prefixWord, tailWord_1625738, baseEnd_1625738] using wordTrace_append hprefix tailTrace_1625738
  have hstable : (prefixWord ++ tailWord_1625738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625738).length < 2 ^ (prefixWord ++ tailWord_1625738).sum := by decide
  have hdescent : baseEnd_1625738 < baseStart_1625738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625742 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_1625742 : Nat := 118140960795 + 1625742 * 2 ^ 59
def prefixEnd_1625742 : Nat := 4983230072969 + 3 ^ 40 * 1625742 * 2
def baseEnd_1625742 : Nat := 92754118466875945627595

theorem tailTrace_1625742 : CollatzResearch.WordTrace tailWord_1625742 prefixEnd_1625742 92754118466875945627595 := by
  unfold tailWord_1625742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7411960259527732934186935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39530454717481242315663653 7411960259527732934186935)
  ·
    refine ⟨11117940389291599401280403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7411960259527732934186935 11117940389291599401280403)
    ·
      refine ⟨16676910583937399101920605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11117940389291599401280403 16676910583937399101920605)
      ·
        refine ⟨6253841468976524663220227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16676910583937399101920605 6253841468976524663220227)
        ·
          refine ⟨9380762203464786994830341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253841468976524663220227 9380762203464786994830341)
          ·
            refine ⟨1758892913149647561530689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9380762203464786994830341 1758892913149647561530689)
            ·
              refine ⟨1319169684862235671148017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1758892913149647561530689 1319169684862235671148017)
              ·
                refine ⟨989377263646676753361013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319169684862235671148017 989377263646676753361013)
                ·
                  refine ⟨92754118466875945627595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 989377263646676753361013 92754118466875945627595)
                  ·
                    rfl

theorem cell23_1625742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_1625742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625742 prefixEnd_1625742 := by exact prefixLift 1625742
  have htrace : WordTrace (prefixWord ++ tailWord_1625742) baseStart_1625742 baseEnd_1625742 := by
    simpa [prefixWord, tailWord_1625742, baseEnd_1625742] using wordTrace_append hprefix tailTrace_1625742
  have hstable : (prefixWord ++ tailWord_1625742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625742).length < 2 ^ (prefixWord ++ tailWord_1625742).sum := by decide
  have hdescent : baseEnd_1625742 < baseStart_1625742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625785 : List Nat := [1, 2, 1, 4, 1, 1, 3, 5, 1, 4]
def baseStart_1625785 : Nat := 118140960795 + 1625785 * 2 ^ 59
def prefixEnd_1625785 : Nat := 4983230072969 + 3 ^ 40 * 1625785 * 2
def baseEnd_1625785 : Nat := 278269715290008947470219

theorem tailTrace_1625785 : CollatzResearch.WordTrace tailWord_1625785 prefixEnd_1625785 278269715290008947470219 := by
  unfold tailWord_1625785
  simp only [CollatzResearch.WordTrace]
  refine ⟨59297250415066081817310809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39531500276710721211540539 59297250415066081817310809)
  ·
    refine ⟨44472937811299561362983107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59297250415066081817310809 44472937811299561362983107)
    ·
      refine ⟨66709406716949342044474661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44472937811299561362983107 66709406716949342044474661)
      ·
        refine ⟨12508013759428001633338999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66709406716949342044474661 12508013759428001633338999)
        ·
          refine ⟨18762020639142002450008499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12508013759428001633338999 18762020639142002450008499)
          ·
            refine ⟨28143030958713003675012749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18762020639142002450008499 28143030958713003675012749)
            ·
              refine ⟨10553636609517376378129781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28143030958713003675012749 10553636609517376378129781)
              ·
                refine ⟨989403432142254035449667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10553636609517376378129781 989403432142254035449667)
                ·
                  refine ⟨1484105148213381053174501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989403432142254035449667 1484105148213381053174501)
                  ·
                    refine ⟨278269715290008947470219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1484105148213381053174501 278269715290008947470219)
                    ·
                      rfl

theorem cell23_1625785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 1, 4].length) (baseStart_1625785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625785 prefixEnd_1625785 := by exact prefixLift 1625785
  have htrace : WordTrace (prefixWord ++ tailWord_1625785) baseStart_1625785 baseEnd_1625785 := by
    simpa [prefixWord, tailWord_1625785, baseEnd_1625785] using wordTrace_append hprefix tailTrace_1625785
  have hstable : (prefixWord ++ tailWord_1625785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625785).length < 2 ^ (prefixWord ++ tailWord_1625785).sum := by decide
  have hdescent : baseEnd_1625785 < baseStart_1625785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625868 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1625868 : Nat := 118140960795 + 1625868 * 2 ^ 59
def prefixEnd_1625868 : Nat := 4983230072969 + 3 ^ 40 * 1625868 * 2
def baseEnd_1625868 : Nat := 834851764764350017672775

theorem tailTrace_1625868 : CollatzResearch.WordTrace tailWord_1625868 prefixEnd_1625868 834851764764350017672775 := by
  unfold tailWord_1625868
  simp only [CollatzResearch.WordTrace]
  refine ⟨29650138836882693496291129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39533518449176924661721505 29650138836882693496291129)
  ·
    refine ⟨22237604127662020122218347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29650138836882693496291129 22237604127662020122218347)
    ·
      refine ⟨33356406191493030183327521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22237604127662020122218347 33356406191493030183327521)
      ·
        refine ⟨25017304643619772637495641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33356406191493030183327521 25017304643619772637495641)
        ·
          refine ⟨18762978482714829478121731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25017304643619772637495641 18762978482714829478121731)
          ·
            refine ⟨28144467724072244217182597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18762978482714829478121731 28144467724072244217182597)
            ·
              refine ⟨5277087698263545790721737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28144467724072244217182597 5277087698263545790721737)
              ·
                refine ⟨3957815773697659343041303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5277087698263545790721737 3957815773697659343041303)
                ·
                  refine ⟨5936723660546489014561955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957815773697659343041303 5936723660546489014561955)
                  ·
                    refine ⟨8905085490819733521842933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5936723660546489014561955 8905085490819733521842933)
                    ·
                      refine ⟨834851764764350017672775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8905085490819733521842933 834851764764350017672775)
                      ·
                        rfl

theorem cell23_1625868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1625868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625868 prefixEnd_1625868 := by exact prefixLift 1625868
  have htrace : WordTrace (prefixWord ++ tailWord_1625868) baseStart_1625868 baseEnd_1625868 := by
    simpa [prefixWord, tailWord_1625868, baseEnd_1625868] using wordTrace_append hprefix tailTrace_1625868
  have hstable : (prefixWord ++ tailWord_1625868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625868).length < 2 ^ (prefixWord ++ tailWord_1625868).sum := by decide
  have hdescent : baseEnd_1625868 < baseStart_1625868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625882 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_1625882 : Nat := 118140960795 + 1625882 * 2 ^ 59
def prefixEnd_1625882 : Nat := 4983230072969 + 3 ^ 40 * 1625882 * 2
def baseEnd_1625882 : Nat := 834858953493512962897711

theorem tailTrace_1625882 : CollatzResearch.WordTrace tailWord_1625882 prefixEnd_1625882 834858953493512962897711 := by
  unfold tailWord_1625882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14825197073928666845897975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39533858863809778255727933 14825197073928666845897975)
  ·
    refine ⟨22237795610893000268846963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14825197073928666845897975 22237795610893000268846963)
    ·
      refine ⟨33356693416339500403270445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22237795610893000268846963 33356693416339500403270445)
      ·
        refine ⟨12508760031127312651226417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33356693416339500403270445 12508760031127312651226417)
        ·
          refine ⟨9381570023345484488419813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12508760031127312651226417 9381570023345484488419813)
          ·
            refine ⟨1759044379377278341578715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9381570023345484488419813 1759044379377278341578715)
            ·
              refine ⟨2638566569065917512368073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759044379377278341578715 2638566569065917512368073)
              ·
                refine ⟨1978924926799438134276055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638566569065917512368073 1978924926799438134276055)
                ·
                  refine ⟨2968387390199157201414083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978924926799438134276055 2968387390199157201414083)
                  ·
                    refine ⟨4452581085298735802121125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2968387390199157201414083 4452581085298735802121125)
                    ·
                      refine ⟨834858953493512962897711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4452581085298735802121125 834858953493512962897711)
                      ·
                        rfl

theorem cell23_1625882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_1625882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625882 prefixEnd_1625882 := by exact prefixLift 1625882
  have htrace : WordTrace (prefixWord ++ tailWord_1625882) baseStart_1625882 baseEnd_1625882 := by
    simpa [prefixWord, tailWord_1625882, baseEnd_1625882] using wordTrace_append hprefix tailTrace_1625882
  have hstable : (prefixWord ++ tailWord_1625882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625882).length < 2 ^ (prefixWord ++ tailWord_1625882).sum := by decide
  have hdescent : baseEnd_1625882 < baseStart_1625882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625916 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_1625916 : Nat := 118140960795 + 1625916 * 2 ^ 59
def prefixEnd_1625916 : Nat := 4983230072969 + 3 ^ 40 * 1625916 * 2
def baseEnd_1625916 : Nat := 834876411835765829872555

theorem tailTrace_1625916 : CollatzResearch.WordTrace tailWord_1625916 prefixEnd_1625916 834876411835765829872555 := by
  unfold tailWord_1625916
  simp only [CollatzResearch.WordTrace]
  refine ⟨29651014188795745595164801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39534685585060994126886401 29651014188795745595164801)
  ·
    refine ⟨22238260641596809196373601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29651014188795745595164801 22238260641596809196373601)
    ·
      refine ⟨16678695481197606897280201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22238260641596809196373601 16678695481197606897280201)
      ·
        refine ⟨12509021610898205172960151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16678695481197606897280201 12509021610898205172960151)
        ·
          refine ⟨18763532416347307759440227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12509021610898205172960151 18763532416347307759440227)
          ·
            refine ⟨28145298624520961639160341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18763532416347307759440227 28145298624520961639160341)
            ·
              refine ⟨1319310873024420076835641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28145298624520961639160341 1319310873024420076835641)
              ·
                refine ⟨989483154768315057626731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319310873024420076835641 989483154768315057626731)
                ·
                  refine ⟨1484224732152472586440097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989483154768315057626731 1484224732152472586440097)
                  ·
                    refine ⟨1113168549114354439830073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1484224732152472586440097 1113168549114354439830073)
                    ·
                      refine ⟨834876411835765829872555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113168549114354439830073 834876411835765829872555)
                      ·
                        rfl

theorem cell23_1625916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_1625916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625916 prefixEnd_1625916 := by exact prefixLift 1625916
  have htrace : WordTrace (prefixWord ++ tailWord_1625916) baseStart_1625916 baseEnd_1625916 := by
    simpa [prefixWord, tailWord_1625916, baseEnd_1625916] using wordTrace_append hprefix tailTrace_1625916
  have hstable : (prefixWord ++ tailWord_1625916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625916).length < 2 ^ (prefixWord ++ tailWord_1625916).sum := by decide
  have hdescent : baseEnd_1625916 < baseStart_1625916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625925 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 5, 3, 2]
def baseStart_1625925 : Nat := 118140960795 + 1625925 * 2 ^ 59
def prefixEnd_1625925 : Nat := 4983230072969 + 3 ^ 40 * 1625925 * 2
def baseEnd_1625925 : Nat := 834881033161656294660013

theorem tailTrace_1625925 : CollatzResearch.WordTrace tailWord_1625925 prefixEnd_1625925 834881033161656294660013 := by
  unfold tailWord_1625925
  simp only [CollatzResearch.WordTrace]
  refine ⟨59302356634558885727407229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39534904423039257151604819 59302356634558885727407229)
  ·
    refine ⟨22238383737959582147777711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59302356634558885727407229 22238383737959582147777711)
    ·
      refine ⟨33357575606939373221666567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22238383737959582147777711 33357575606939373221666567)
      ·
        refine ⟨50036363410409059832499851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33357575606939373221666567 50036363410409059832499851)
        ·
          refine ⟨75054545115613589748749777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50036363410409059832499851 75054545115613589748749777)
          ·
            refine ⟨56290908836710192311562333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75054545115613589748749777 56290908836710192311562333)
            ·
              refine ⟨21109090813766322116835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56290908836710192311562333 21109090813766322116835875)
              ·
                refine ⟨31663636220649483175253813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21109090813766322116835875 31663636220649483175253813)
                ·
                  refine ⟨2968465895685889047680045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31663636220649483175253813 2968465895685889047680045)
                  ·
                    refine ⟨1113174710882208392880017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2968465895685889047680045 1113174710882208392880017)
                    ·
                      refine ⟨834881033161656294660013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113174710882208392880017 834881033161656294660013)
                      ·
                        rfl

theorem cell23_1625925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_1625925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625925 prefixEnd_1625925 := by exact prefixLift 1625925
  have htrace : WordTrace (prefixWord ++ tailWord_1625925) baseStart_1625925 baseEnd_1625925 := by
    simpa [prefixWord, tailWord_1625925, baseEnd_1625925] using wordTrace_append hprefix tailTrace_1625925
  have hstable : (prefixWord ++ tailWord_1625925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625925).length < 2 ^ (prefixWord ++ tailWord_1625925).sum := by decide
  have hdescent : baseEnd_1625925 < baseStart_1625925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625932 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1625932 : Nat := 118140960795 + 1625932 * 2 ^ 59
def prefixEnd_1625932 : Nat := 4983230072969 + 3 ^ 40 * 1625932 * 2
def baseEnd_1625932 : Nat := 834884627526237767272481

theorem tailTrace_1625932 : CollatzResearch.WordTrace tailWord_1625932 prefixEnd_1625932 834884627526237767272481 := by
  unfold tailWord_1625932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29651305972766762961456025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39535074630355683948608033 29651305972766762961456025)
  ·
    refine ⟨22238479479575072221092019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29651305972766762961456025 22238479479575072221092019)
    ·
      refine ⟨33357719219362608331638029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22238479479575072221092019 33357719219362608331638029)
      ·
        refine ⟨12509144707260978124364261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33357719219362608331638029 12509144707260978124364261)
        ·
          refine ⟨2345464632611433398318299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12509144707260978124364261 2345464632611433398318299)
          ·
            refine ⟨3518196948917150097477449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345464632611433398318299 3518196948917150097477449)
            ·
              refine ⟨2638647711687862573108087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518196948917150097477449 2638647711687862573108087)
              ·
                refine ⟨3957971567531793859662131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638647711687862573108087 3957971567531793859662131)
                ·
                  refine ⟨5936957351297690789493197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3957971567531793859662131 5936957351297690789493197)
                  ·
                    refine ⟨2226359006736634046059949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5936957351297690789493197 2226359006736634046059949)
                    ·
                      refine ⟨834884627526237767272481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2226359006736634046059949 834884627526237767272481)
                      ·
                        rfl

theorem cell23_1625932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1625932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625932 prefixEnd_1625932 := by exact prefixLift 1625932
  have htrace : WordTrace (prefixWord ++ tailWord_1625932) baseStart_1625932 baseEnd_1625932 := by
    simpa [prefixWord, tailWord_1625932, baseEnd_1625932] using wordTrace_append hprefix tailTrace_1625932
  have hstable : (prefixWord ++ tailWord_1625932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625932).length < 2 ^ (prefixWord ++ tailWord_1625932).sum := by decide
  have hdescent : baseEnd_1625932 < baseStart_1625932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625966 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1625966 : Nat := 118140960795 + 1625966 * 2 ^ 59
def prefixEnd_1625966 : Nat := 4983230072969 + 3 ^ 40 * 1625966 * 2
def baseEnd_1625966 : Nat := 834902085868490634247325

theorem tailTrace_1625966 : CollatzResearch.WordTrace tailWord_1625966 prefixEnd_1625966 834902085868490634247325 := by
  unfold tailWord_1625966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412981503426293716206219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39535901351606899819766501 7412981503426293716206219)
  ·
    refine ⟨11119472255139440574309329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412981503426293716206219 11119472255139440574309329)
    ·
      refine ⟨8339604191354580430731997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11119472255139440574309329 8339604191354580430731997)
      ·
        refine ⟨3127351571757967661524499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8339604191354580430731997 3127351571757967661524499)
        ·
          refine ⟨4691027357636951492286749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127351571757967661524499 4691027357636951492286749)
          ·
            refine ⟨1759135259113856809607531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4691027357636951492286749 1759135259113856809607531)
            ·
              refine ⟨2638702888670785214411297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759135259113856809607531 2638702888670785214411297)
              ·
                refine ⟨1979027166503088910808473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638702888670785214411297 1979027166503088910808473)
                ·
                  refine ⟨1484270374877316683106355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979027166503088910808473 1484270374877316683106355)
                  ·
                    refine ⟨2226405562315975024659533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484270374877316683106355 2226405562315975024659533)
                    ·
                      refine ⟨834902085868490634247325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2226405562315975024659533 834902085868490634247325)
                      ·
                        rfl

theorem cell23_1625966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1625966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625966 prefixEnd_1625966 := by exact prefixLift 1625966
  have htrace : WordTrace (prefixWord ++ tailWord_1625966) baseStart_1625966 baseEnd_1625966 := by
    simpa [prefixWord, tailWord_1625966, baseEnd_1625966] using wordTrace_append hprefix tailTrace_1625966
  have hstable : (prefixWord ++ tailWord_1625966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625966).length < 2 ^ (prefixWord ++ tailWord_1625966).sum := by decide
  have hdescent : baseEnd_1625966 < baseStart_1625966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625978 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_1625978 : Nat := 118140960795 + 1625978 * 2 ^ 59
def prefixEnd_1625978 : Nat := 4983230072969 + 3 ^ 40 * 1625978 * 2
def baseEnd_1625978 : Nat := 92767583070704954144141

theorem tailTrace_1625978 : CollatzResearch.WordTrace tailWord_1625978 prefixEnd_1625978 92767583070704954144141 := by
  unfold tailWord_1625978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14826072425841718944771647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39536193135577917186057725 14826072425841718944771647)
  ·
    refine ⟨22239108638762578417157471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14826072425841718944771647 22239108638762578417157471)
    ·
      refine ⟨33358662958143867625736207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22239108638762578417157471 33358662958143867625736207)
      ·
        refine ⟨50037994437215801438604311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33358662958143867625736207 50037994437215801438604311)
        ·
          refine ⟨75056991655823702157906467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50037994437215801438604311 75056991655823702157906467)
          ·
            refine ⟨112585487483735553236859701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75056991655823702157906467 112585487483735553236859701)
            ·
              refine ⟨10554889451600208115955597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112585487483735553236859701 10554889451600208115955597)
              ·
                refine ⟨3958083544350078043483349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10554889451600208115955597 3958083544350078043483349)
                ·
                  refine ⟨92767583070704954144141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3958083544350078043483349 92767583070704954144141)
                  ·
                    rfl

theorem cell23_1625978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_1625978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625978 prefixEnd_1625978 := by exact prefixLift 1625978
  have htrace : WordTrace (prefixWord ++ tailWord_1625978) baseStart_1625978 baseEnd_1625978 := by
    simpa [prefixWord, tailWord_1625978, baseEnd_1625978] using wordTrace_append hprefix tailTrace_1625978
  have hstable : (prefixWord ++ tailWord_1625978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625978).length < 2 ^ (prefixWord ++ tailWord_1625978).sum := by decide
  have hdescent : baseEnd_1625978 < baseStart_1625978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625982 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1625982 : Nat := 118140960795 + 1625982 * 2 ^ 59
def prefixEnd_1625982 : Nat := 4983230072969 + 3 ^ 40 * 1625982 * 2
def baseEnd_1625982 : Nat := 278303433852987523882417

theorem tailTrace_1625982 : CollatzResearch.WordTrace tailWord_1625982 prefixEnd_1625982 278303433852987523882417 := by
  unfold tailWord_1625982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413054449419048057779025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39536290396901589641488133 7413054449419048057779025)
  ·
    refine ⟨5559790837064286043334269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7413054449419048057779025 5559790837064286043334269)
    ·
      refine ⟨2084921563899107266250351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5559790837064286043334269 2084921563899107266250351)
      ·
        refine ⟨3127382345848660899375527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084921563899107266250351 3127382345848660899375527)
        ·
          refine ⟨4691073518772991349063291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127382345848660899375527 4691073518772991349063291)
          ·
            refine ⟨7036610278159487023594937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691073518772991349063291 7036610278159487023594937)
            ·
              refine ⟨5277457708619615267696203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7036610278159487023594937 5277457708619615267696203)
              ·
                refine ⟨7916186562929422901544305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5277457708619615267696203 7916186562929422901544305)
                ·
                  refine ⟨5937139922197067176158229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7916186562929422901544305 5937139922197067176158229)
                  ·
                    refine ⟨278303433852987523882417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5937139922197067176158229 278303433852987523882417)
                    ·
                      rfl

theorem cell23_1625982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1625982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1625982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1625982 prefixEnd_1625982 := by exact prefixLift 1625982
  have htrace : WordTrace (prefixWord ++ tailWord_1625982) baseStart_1625982 baseEnd_1625982 := by
    simpa [prefixWord, tailWord_1625982, baseEnd_1625982] using wordTrace_append hprefix tailTrace_1625982
  have hstable : (prefixWord ++ tailWord_1625982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625982).length < 2 ^ (prefixWord ++ tailWord_1625982).sum := by decide
  have hdescent : baseEnd_1625982 < baseStart_1625982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626055 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 5, 4]
def baseStart_1626055 : Nat := 118140960795 + 1626055 * 2 ^ 59
def prefixEnd_1626055 : Nat := 4983230072969 + 3 ^ 40 * 1626055 * 2
def baseEnd_1626055 : Nat := 278315928548913595344805

theorem tailTrace_1626055 : CollatzResearch.WordTrace tailWord_1626055 prefixEnd_1626055 278315928548913595344805 := by
  unfold tailWord_1626055
  simp only [CollatzResearch.WordTrace]
  refine ⟨59307098124087917929639619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39538065416058611953093079 59307098124087917929639619)
  ·
    refine ⟨88960647186131876894459429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59307098124087917929639619 88960647186131876894459429)
    ·
      refine ⟨16680121347399726917711143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88960647186131876894459429 16680121347399726917711143)
      ·
        refine ⟨25020182021099590376566715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16680121347399726917711143 25020182021099590376566715)
        ·
          refine ⟨37530273031649385564850073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25020182021099590376566715 37530273031649385564850073)
          ·
            refine ⟨28147704773737039173637555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37530273031649385564850073 28147704773737039173637555)
            ·
              refine ⟨42221557160605558760456333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28147704773737039173637555 42221557160605558760456333)
              ·
                refine ⟨15833083935227084535171125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42221557160605558760456333 15833083935227084535171125)
                ·
                  refine ⟨1484351618927539175172293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15833083935227084535171125 1484351618927539175172293)
                  ·
                    refine ⟨278315928548913595344805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1484351618927539175172293 278315928548913595344805)
                    ·
                      rfl

theorem cell23_1626055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_1626055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626055 prefixEnd_1626055 := by exact prefixLift 1626055
  have htrace : WordTrace (prefixWord ++ tailWord_1626055) baseStart_1626055 baseEnd_1626055 := by
    simpa [prefixWord, tailWord_1626055, baseEnd_1626055] using wordTrace_append hprefix tailTrace_1626055
  have hstable : (prefixWord ++ tailWord_1626055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626055).length < 2 ^ (prefixWord ++ tailWord_1626055).sum := by decide
  have hdescent : baseEnd_1626055 < baseStart_1626055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626062 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1626062 : Nat := 118140960795 + 1626062 * 2 ^ 59
def prefixEnd_1626062 : Nat := 4983230072969 + 3 ^ 40 * 1626062 * 2
def baseEnd_1626062 : Nat := 834951380011322258646883

theorem tailTrace_1626062 : CollatzResearch.WordTrace tailWord_1626062 prefixEnd_1626062 834951380011322258646883 := by
  unfold tailWord_1626062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413419179382819765643055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39538235623375038750096293 7413419179382819765643055)
  ·
    refine ⟨11120128769074229648464583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7413419179382819765643055 11120128769074229648464583)
    ·
      refine ⟨16680193153611344472696875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11120128769074229648464583 16680193153611344472696875)
      ·
        refine ⟨25020289730417016709045313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16680193153611344472696875 25020289730417016709045313)
        ·
          refine ⟨18765217297812762531783985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25020289730417016709045313 18765217297812762531783985)
          ·
            refine ⟨14073912973359571898837989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18765217297812762531783985 14073912973359571898837989)
            ·
              refine ⟨2638858682504919731032123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14073912973359571898837989 2638858682504919731032123)
              ·
                refine ⟨3958288023757379596548185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638858682504919731032123 3958288023757379596548185)
                ·
                  refine ⟨2968716017818034697411139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3958288023757379596548185 2968716017818034697411139)
                  ·
                    refine ⟨4453074026727052046116709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2968716017818034697411139 4453074026727052046116709)
                    ·
                      refine ⟨834951380011322258646883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4453074026727052046116709 834951380011322258646883)
                      ·
                        rfl

theorem cell23_1626062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1626062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626062 prefixEnd_1626062 := by exact prefixLift 1626062
  have htrace : WordTrace (prefixWord ++ tailWord_1626062) baseStart_1626062 baseEnd_1626062 := by
    simpa [prefixWord, tailWord_1626062, baseEnd_1626062] using wordTrace_append hprefix tailTrace_1626062
  have hstable : (prefixWord ++ tailWord_1626062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626062).length < 2 ^ (prefixWord ++ tailWord_1626062).sum := by decide
  have hdescent : baseEnd_1626062 < baseStart_1626062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626146 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_1626146 : Nat := 118140960795 + 1626146 * 2 ^ 59
def prefixEnd_1626146 : Nat := 4983230072969 + 3 ^ 40 * 1626146 * 2
def baseEnd_1626146 : Nat := 834994512386299929996497

theorem tailTrace_1626146 : CollatzResearch.WordTrace tailWord_1626146 prefixEnd_1626146 834994512386299929996497 := by
  unfold tailWord_1626146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827604291689560117800573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39540278111172160314134861 14827604291689560117800573)
  ·
    refine ⟨5560351609383585044175215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14827604291689560117800573 5560351609383585044175215)
    ·
      refine ⟨8340527414075377566262823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560351609383585044175215 8340527414075377566262823)
      ·
        refine ⟨12510791121113066349394235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8340527414075377566262823 12510791121113066349394235)
        ·
          refine ⟨18766186681669599524091353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12510791121113066349394235 18766186681669599524091353)
          ·
            refine ⟨14074640011252199643068515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18766186681669599524091353 14074640011252199643068515)
            ·
              refine ⟨21111960016878299464602773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14074640011252199643068515 21111960016878299464602773)
              ·
                refine ⟨989623125791170287403255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21111960016878299464602773 989623125791170287403255)
                ·
                  refine ⟨1484434688686755431104883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989623125791170287403255 1484434688686755431104883)
                  ·
                    refine ⟨2226652033030133146657325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484434688686755431104883 2226652033030133146657325)
                    ·
                      refine ⟨834994512386299929996497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2226652033030133146657325 834994512386299929996497)
                      ·
                        rfl

theorem cell23_1626146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_1626146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626146 prefixEnd_1626146 := by exact prefixLift 1626146
  have htrace : WordTrace (prefixWord ++ tailWord_1626146) baseStart_1626146 baseEnd_1626146 := by
    simpa [prefixWord, tailWord_1626146, baseEnd_1626146] using wordTrace_append hprefix tailTrace_1626146
  have hstable : (prefixWord ++ tailWord_1626146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626146).length < 2 ^ (prefixWord ++ tailWord_1626146).sum := by decide
  have hdescent : baseEnd_1626146 < baseStart_1626146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626155 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 3]
def baseStart_1626155 : Nat := 118140960795 + 1626155 * 2 ^ 59
def prefixEnd_1626155 : Nat := 4983230072969 + 3 ^ 40 * 1626155 * 2
def baseEnd_1626155 : Nat := 834999133712190394783955

theorem tailTrace_1626155 : CollatzResearch.WordTrace tailWord_1626155 prefixEnd_1626155 834999133712190394783955 := by
  unfold tailWord_1626155
  simp only [CollatzResearch.WordTrace]
  refine ⟨59310745423725635008279919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39540496949150423338853279 59310745423725635008279919)
  ·
    refine ⟨88966118135588452512419879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59310745423725635008279919 88966118135588452512419879)
    ·
      refine ⟨133449177203382678768629819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88966118135588452512419879 133449177203382678768629819)
      ·
        refine ⟨200173765805074018152944729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133449177203382678768629819 200173765805074018152944729)
        ·
          refine ⟨150130324353805513614708547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200173765805074018152944729 150130324353805513614708547)
          ·
            refine ⟨225195486530708270422062821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150130324353805513614708547 225195486530708270422062821)
            ·
              refine ⟨42224153724507800704136779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225195486530708270422062821 42224153724507800704136779)
              ·
                refine ⟨63336230586761701056205169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42224153724507800704136779 63336230586761701056205169)
                ·
                  refine ⟨47502172940071275792153877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63336230586761701056205169 47502172940071275792153877)
                  ·
                    refine ⟨2226664356565841052757213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47502172940071275792153877 2226664356565841052757213)
                    ·
                      refine ⟨834999133712190394783955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2226664356565841052757213 834999133712190394783955)
                      ·
                        rfl

theorem cell23_1626155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 3].length) (baseStart_1626155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626155 prefixEnd_1626155 := by exact prefixLift 1626155
  have htrace : WordTrace (prefixWord ++ tailWord_1626155) baseStart_1626155 baseEnd_1626155 := by
    simpa [prefixWord, tailWord_1626155, baseEnd_1626155] using wordTrace_append hprefix tailTrace_1626155
  have hstable : (prefixWord ++ tailWord_1626155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626155).length < 2 ^ (prefixWord ++ tailWord_1626155).sum := by decide
  have hdescent : baseEnd_1626155 < baseStart_1626155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626162 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_1626162 : Nat := 118140960795 + 1626162 * 2 ^ 59
def prefixEnd_1626162 : Nat := 4983230072969 + 3 ^ 40 * 1626162 * 2
def baseEnd_1626162 : Nat := 278334242692257289132141

theorem tailTrace_1626162 : CollatzResearch.WordTrace tailWord_1626162 prefixEnd_1626162 278334242692257289132141 := by
  unfold tailWord_1626162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827750183675068800946185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39540667156466850135856493 14827750183675068800946185)
  ·
    refine ⟨11120812637756301600709639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14827750183675068800946185 11120812637756301600709639)
    ·
      refine ⟨16681218956634452401064459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11120812637756301600709639 16681218956634452401064459)
      ·
        refine ⟨25021828434951678601596689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16681218956634452401064459 25021828434951678601596689)
        ·
          refine ⟨18766371326213758951197517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25021828434951678601596689 18766371326213758951197517)
          ·
            refine ⟨7037389247330159606699069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18766371326213758951197517 7037389247330159606699069)
            ·
              refine ⟨2639020967748809852512151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7037389247330159606699069 2639020967748809852512151)
              ·
                refine ⟨3958531451623214778768227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639020967748809852512151 3958531451623214778768227)
                ·
                  refine ⟨5937797177434822168152341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958531451623214778768227 5937797177434822168152341)
                  ·
                    refine ⟨278334242692257289132141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5937797177434822168152341 278334242692257289132141)
                    ·
                      rfl

theorem cell23_1626162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_1626162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626162 prefixEnd_1626162 := by exact prefixLift 1626162
  have htrace : WordTrace (prefixWord ++ tailWord_1626162) baseStart_1626162 baseEnd_1626162 := by
    simpa [prefixWord, tailWord_1626162, baseEnd_1626162] using wordTrace_append hprefix tailTrace_1626162
  have hstable : (prefixWord ++ tailWord_1626162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626162).length < 2 ^ (prefixWord ++ tailWord_1626162).sum := by decide
  have hdescent : baseEnd_1626162 < baseStart_1626162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626189 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1626189 : Nat := 118140960795 + 1626189 * 2 ^ 59
def prefixEnd_1626189 : Nat := 4983230072969 + 3 ^ 40 * 1626189 * 2
def baseEnd_1626189 : Nat := 835016592054443261758799

theorem tailTrace_1626189 : CollatzResearch.WordTrace tailWord_1626189 prefixEnd_1626189 835016592054443261758799 := by
  unfold tailWord_1626189
  simp only [CollatzResearch.WordTrace]
  refine ⟨59311985505602458815017621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39541323670401639210011747 59311985505602458815017621)
  ·
    refine ⟨2780249320575115256953951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59311985505602458815017621 2780249320575115256953951)
    ·
      refine ⟨4170373980862672885430927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780249320575115256953951 4170373980862672885430927)
      ·
        refine ⟨6255560971294009328146391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170373980862672885430927 6255560971294009328146391)
        ·
          refine ⟨9383341456941013992219587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255560971294009328146391 9383341456941013992219587)
          ·
            refine ⟨14075012185411520988329381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9383341456941013992219587 14075012185411520988329381)
            ·
              refine ⟨2639064784764660185311759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14075012185411520988329381 2639064784764660185311759)
              ·
                refine ⟨3958597177146990277967639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639064784764660185311759 3958597177146990277967639)
                ·
                  refine ⟨5937895765720485416951459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3958597177146990277967639 5937895765720485416951459)
                  ·
                    refine ⟨8906843648580728125427189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5937895765720485416951459 8906843648580728125427189)
                    ·
                      refine ⟨835016592054443261758799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8906843648580728125427189 835016592054443261758799)
                      ·
                        rfl

theorem cell23_1626189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1626189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626189 prefixEnd_1626189 := by exact prefixLift 1626189
  have htrace : WordTrace (prefixWord ++ tailWord_1626189) baseStart_1626189 baseEnd_1626189 := by
    simpa [prefixWord, tailWord_1626189, baseEnd_1626189] using wordTrace_append hprefix tailTrace_1626189
  have hstable : (prefixWord ++ tailWord_1626189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626189).length < 2 ^ (prefixWord ++ tailWord_1626189).sum := by decide
  have hdescent : baseEnd_1626189 < baseStart_1626189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626235 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 6, 6]
def baseStart_1626235 : Nat := 118140960795 + 1626235 * 2 ^ 59
def prefixEnd_1626235 : Nat := 4983230072969 + 3 ^ 40 * 1626235 * 2
def baseEnd_1626235 : Nat := 278346737388183360594529

theorem tailTrace_1626235 : CollatzResearch.WordTrace tailWord_1626235 prefixEnd_1626235 278346737388183360594529 := by
  unfold tailWord_1626235
  simp only [CollatzResearch.WordTrace]
  refine ⟨59313663263435808671192159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39542442175623872447461439 59313663263435808671192159)
  ·
    refine ⟨88970494895153713006788239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59313663263435808671192159 88970494895153713006788239)
    ·
      refine ⟨133455742342730569510182359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88970494895153713006788239 133455742342730569510182359)
      ·
        refine ⟨200183613514095854265273539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133455742342730569510182359 200183613514095854265273539)
        ·
          refine ⟨300275420271143781397910309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200183613514095854265273539 300275420271143781397910309)
          ·
            refine ⟨56301641300839459012108183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300275420271143781397910309 56301641300839459012108183)
            ·
              refine ⟨84452461951259188518162275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56301641300839459012108183 84452461951259188518162275)
              ·
                refine ⟨126678692926888782777243413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84452461951259188518162275 126678692926888782777243413)
                ·
                  refine ⟨5938063730947911692683285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126678692926888782777243413 5938063730947911692683285)
                  ·
                    refine ⟨278346737388183360594529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5938063730947911692683285 278346737388183360594529)
                    ·
                      rfl

theorem cell23_1626235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_1626235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626235 prefixEnd_1626235 := by exact prefixLift 1626235
  have htrace : WordTrace (prefixWord ++ tailWord_1626235) baseStart_1626235 baseEnd_1626235 := by
    simpa [prefixWord, tailWord_1626235, baseEnd_1626235] using wordTrace_append hprefix tailTrace_1626235
  have hstable : (prefixWord ++ tailWord_1626235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626235).length < 2 ^ (prefixWord ++ tailWord_1626235).sum := by decide
  have hdescent : baseEnd_1626235 < baseStart_1626235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626254 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1626254 : Nat := 118140960795 + 1626254 * 2 ^ 59
def prefixEnd_1626254 : Nat := 4983230072969 + 3 ^ 40 * 1626254 * 2
def baseEnd_1626254 : Nat := 835049968296985507446001

theorem tailTrace_1626254 : CollatzResearch.WordTrace tailWord_1626254 prefixEnd_1626254 835049968296985507446001 := by
  unfold tailWord_1626254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414294531295871864516727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39542904166911316610755877 7414294531295871864516727)
  ·
    refine ⟨11121441796943807796775091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7414294531295871864516727 11121441796943807796775091)
    ·
      refine ⟨16682162695415711695162637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11121441796943807796775091 16682162695415711695162637)
      ·
        refine ⟨6255811010780891885685989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16682162695415711695162637 6255811010780891885685989)
        ·
          refine ⟨1172964564521417228566123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6255811010780891885685989 1172964564521417228566123)
          ·
            refine ⟨1759446846782125842849185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172964564521417228566123 1759446846782125842849185)
            ·
              refine ⟨1319585135086594382136889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759446846782125842849185 1319585135086594382136889)
              ·
                refine ⟨989688851314945786602667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319585135086594382136889 989688851314945786602667)
                ·
                  refine ⟨1484533276972418679904001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989688851314945786602667 1484533276972418679904001)
                  ·
                    refine ⟨1113399957729314009928001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1484533276972418679904001 1113399957729314009928001)
                    ·
                      refine ⟨835049968296985507446001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113399957729314009928001 835049968296985507446001)
                      ·
                        rfl

theorem cell23_1626254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1626254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626254 prefixEnd_1626254 := by exact prefixLift 1626254
  have htrace : WordTrace (prefixWord ++ tailWord_1626254) baseStart_1626254 baseEnd_1626254 := by
    simpa [prefixWord, tailWord_1626254, baseEnd_1626254] using wordTrace_append hprefix tailTrace_1626254
  have hstable : (prefixWord ++ tailWord_1626254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626254).length < 2 ^ (prefixWord ++ tailWord_1626254).sum := by decide
  have hdescent : baseEnd_1626254 < baseStart_1626254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626265 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 11]
def baseStart_1626265 : Nat := 118140960795 + 1626265 * 2 ^ 59
def prefixEnd_1626265 : Nat := 4983230072969 + 3 ^ 40 * 1626265 * 2
def baseEnd_1626265 : Nat := 92783957398242773823161

theorem tailTrace_1626265 : CollatzResearch.WordTrace tailWord_1626265 prefixEnd_1626265 92783957398242773823161 := by
  unfold tailWord_1626265
  simp only [CollatzResearch.WordTrace]
  refine ⟨59314757453327123794784249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39543171635551415863189499 59314757453327123794784249)
  ·
    refine ⟨44486068089995342846088187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59314757453327123794784249 44486068089995342846088187)
    ·
      refine ⟨66729102134993014269132281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44486068089995342846088187 66729102134993014269132281)
      ·
        refine ⟨50046826601244760701849211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66729102134993014269132281 50046826601244760701849211)
        ·
          refine ⟨75070239901867141052773817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50046826601244760701849211 75070239901867141052773817)
          ·
            refine ⟨56302679926400355789580363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75070239901867141052773817 56302679926400355789580363)
            ·
              refine ⟨84454019889600533684370545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56302679926400355789580363 84454019889600533684370545)
              ·
                refine ⟨63340514917200400263277909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84454019889600533684370545 63340514917200400263277909)
                ·
                  refine ⟨92783957398242773823161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 63340514917200400263277909 92783957398242773823161)
                  ·
                    rfl

theorem cell23_1626265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_1626265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626265 prefixEnd_1626265 := by exact prefixLift 1626265
  have htrace : WordTrace (prefixWord ++ tailWord_1626265) baseStart_1626265 baseEnd_1626265 := by
    simpa [prefixWord, tailWord_1626265, baseEnd_1626265] using wordTrace_append hprefix tailTrace_1626265
  have hstable : (prefixWord ++ tailWord_1626265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626265).length < 2 ^ (prefixWord ++ tailWord_1626265).sum := by decide
  have hdescent : baseEnd_1626265 < baseStart_1626265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626272 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1626272 : Nat := 118140960795 + 1626272 * 2 ^ 59
def prefixEnd_1626272 : Nat := 4983230072969 + 3 ^ 40 * 1626272 * 2
def baseEnd_1626272 : Nat := 835059210948766437020917

theorem tailTrace_1626272 : CollatzResearch.WordTrace tailWord_1626272 prefixEnd_1626272 835059210948766437020917 := by
  unfold tailWord_1626272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29657506382150881995144535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39543341842867842660192713 29657506382150881995144535)
  ·
    refine ⟨44486259573226322992716803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29657506382150881995144535 44486259573226322992716803)
    ·
      refine ⟨66729389359839484489075205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44486259573226322992716803 66729389359839484489075205)
      ·
        refine ⟨12511760504969903341701601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66729389359839484489075205 12511760504969903341701601)
        ·
          refine ⟨9383820378727427506276201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12511760504969903341701601 9383820378727427506276201)
          ·
            refine ⟨7037865284045570629707151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383820378727427506276201 7037865284045570629707151)
            ·
              refine ⟨10556797926068355944560727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7037865284045570629707151 10556797926068355944560727)
              ·
                refine ⟨15835196889102533916841091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10556797926068355944560727 15835196889102533916841091)
                ·
                  refine ⟨23752795333653800875261637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15835196889102533916841091 23752795333653800875261637)
                  ·
                    refine ⟨4453649125060087664111557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23752795333653800875261637 4453649125060087664111557)
                    ·
                      refine ⟨835059210948766437020917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4453649125060087664111557 835059210948766437020917)
                      ·
                        rfl

theorem cell23_1626272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1626272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626272 prefixEnd_1626272 := by exact prefixLift 1626272
  have htrace : WordTrace (prefixWord ++ tailWord_1626272) baseStart_1626272 baseEnd_1626272 := by
    simpa [prefixWord, tailWord_1626272, baseEnd_1626272] using wordTrace_append hprefix tailTrace_1626272
  have hstable : (prefixWord ++ tailWord_1626272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626272).length < 2 ^ (prefixWord ++ tailWord_1626272).sum := by decide
  have hdescent : baseEnd_1626272 < baseStart_1626272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626299 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 5]
def baseStart_1626299 : Nat := 118140960795 + 1626299 * 2 ^ 59
def prefixEnd_1626299 : Nat := 4983230072969 + 3 ^ 40 * 1626299 * 2
def baseEnd_1626299 : Nat := 92785897214048647931477

theorem tailTrace_1626299 : CollatzResearch.WordTrace tailWord_1626299 prefixEnd_1626299 92785897214048647931477 := by
  unfold tailWord_1626299
  simp only [CollatzResearch.WordTrace]
  refine ⟨59315997535203947601521951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39543998356802631734347967 59315997535203947601521951)
  ·
    refine ⟨88973996302805921402282927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59315997535203947601521951 88973996302805921402282927)
    ·
      refine ⟨133460994454208882103424391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88973996302805921402282927 133460994454208882103424391)
      ·
        refine ⟨200191491681313323155136587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133460994454208882103424391 200191491681313323155136587)
        ·
          refine ⟨300287237521969984732704881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200191491681313323155136587 300287237521969984732704881)
          ·
            refine ⟨225215428141477488549528661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300287237521969984732704881 225215428141477488549528661)
            ·
              refine ⟨2639243298532939318939789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 225215428141477488549528661 2639243298532939318939789)
              ·
                refine ⟨989716236949852244602421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2639243298532939318939789 989716236949852244602421)
                ·
                  refine ⟨92785897214048647931477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 989716236949852244602421 92785897214048647931477)
                  ·
                    rfl

theorem cell23_1626299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 5].length) (baseStart_1626299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626299 prefixEnd_1626299 := by exact prefixLift 1626299
  have htrace : WordTrace (prefixWord ++ tailWord_1626299) baseStart_1626299 baseEnd_1626299 := by
    simpa [prefixWord, tailWord_1626299, baseEnd_1626299] using wordTrace_append hprefix tailTrace_1626299
  have hstable : (prefixWord ++ tailWord_1626299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626299).length < 2 ^ (prefixWord ++ tailWord_1626299).sum := by decide
  have hdescent : baseEnd_1626299 < baseStart_1626299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626312 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_1626312 : Nat := 118140960795 + 1626312 * 2 ^ 59
def prefixEnd_1626312 : Nat := 4983230072969 + 3 ^ 40 * 1626312 * 2
def baseEnd_1626312 : Nat := 278359916724982093506911

theorem tailTrace_1626312 : CollatzResearch.WordTrace tailWord_1626312 prefixEnd_1626312 278359916724982093506911 := by
  unfold tailWord_1626312
  simp only [CollatzResearch.WordTrace]
  refine ⟨29658235842078425410872595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39544314456104567214496793 29658235842078425410872595)
  ·
    refine ⟨44487353763117638116308893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29658235842078425410872595 44487353763117638116308893)
    ·
      refine ⟨16682757661169114293615835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44487353763117638116308893 16682757661169114293615835)
      ·
        refine ⟨25024136491753671440423753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16682757661169114293615835 25024136491753671440423753)
        ·
          refine ⟨18768102368815253580317815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25024136491753671440423753 18768102368815253580317815)
          ·
            refine ⟨28152153553222880370476723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18768102368815253580317815 28152153553222880370476723)
            ·
              refine ⟨42228230329834320555715085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28152153553222880370476723 42228230329834320555715085)
              ·
                refine ⟨15835586373687870208393157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42228230329834320555715085 15835586373687870208393157)
                ·
                  refine ⟨2969172445066475664073717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15835586373687870208393157 2969172445066475664073717)
                  ·
                    refine ⟨278359916724982093506911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2969172445066475664073717 278359916724982093506911)
                    ·
                      rfl

theorem cell23_1626312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_1626312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626312 prefixEnd_1626312 := by exact prefixLift 1626312
  have htrace : WordTrace (prefixWord ++ tailWord_1626312) baseStart_1626312 baseEnd_1626312 := by
    simpa [prefixWord, tailWord_1626312, baseEnd_1626312] using wordTrace_append hprefix tailTrace_1626312
  have hstable : (prefixWord ++ tailWord_1626312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626312).length < 2 ^ (prefixWord ++ tailWord_1626312).sum := by decide
  have hdescent : baseEnd_1626312 < baseStart_1626312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626316 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 7]
def baseStart_1626316 : Nat := 118140960795 + 1626316 * 2 ^ 59
def prefixEnd_1626316 : Nat := 4983230072969 + 3 ^ 40 * 1626316 * 2
def baseEnd_1626316 : Nat := 92786867121951584985635

theorem tailTrace_1626316 : CollatzResearch.WordTrace tailWord_1626316 prefixEnd_1626316 92786867121951584985635 := by
  unfold tailWord_1626316
  simp only [CollatzResearch.WordTrace]
  refine ⟨29658308788071179752445401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39544411717428239669927201 29658308788071179752445401)
  ·
    refine ⟨22243731591053384814334051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29658308788071179752445401 22243731591053384814334051)
    ·
      refine ⟨33365597386580077221501077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22243731591053384814334051 33365597386580077221501077)
      ·
        refine ⟨1564012377495941119757863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33365597386580077221501077 1564012377495941119757863)
        ·
          refine ⟨2346018566243911679636795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564012377495941119757863 2346018566243911679636795)
          ·
            refine ⟨3519027849365867519455193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346018566243911679636795 3519027849365867519455193)
            ·
              refine ⟨2639270887024400639591395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519027849365867519455193 2639270887024400639591395)
              ·
                refine ⟨3958906330536600959387093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639270887024400639591395 3958906330536600959387093)
                ·
                  refine ⟨92786867121951584985635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3958906330536600959387093 92786867121951584985635)
                  ·
                    rfl

theorem cell23_1626316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_1626316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626316 prefixEnd_1626316 := by exact prefixLift 1626316
  have htrace : WordTrace (prefixWord ++ tailWord_1626316) baseStart_1626316 baseEnd_1626316 := by
    simpa [prefixWord, tailWord_1626316, baseEnd_1626316] using wordTrace_append hprefix tailTrace_1626316
  have hstable : (prefixWord ++ tailWord_1626316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626316).length < 2 ^ (prefixWord ++ tailWord_1626316).sum := by decide
  have hdescent : baseEnd_1626316 < baseStart_1626316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626366 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1626366 : Nat := 118140960795 + 1626366 * 2 ^ 59
def prefixEnd_1626366 : Nat := 4983230072969 + 3 ^ 40 * 1626366 * 2
def baseEnd_1626366 : Nat := 835107478130289069245485

theorem tailTrace_1626366 : CollatzResearch.WordTrace tailWord_1626366 prefixEnd_1626366 835107478130289069245485 := by
  unfold tailWord_1626366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414805153245152255526369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39545627483974145362807301 7414805153245152255526369)
  ·
    refine ⟨5561103864933864191644777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7414805153245152255526369 5561103864933864191644777)
    ·
      refine ⟨4170827898700398143733583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5561103864933864191644777 4170827898700398143733583)
      ·
        refine ⟨6256241848050597215600375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170827898700398143733583 6256241848050597215600375)
        ·
          refine ⟨9384362772075895823400563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256241848050597215600375 9384362772075895823400563)
          ·
            refine ⟨14076544158113843735100845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9384362772075895823400563 14076544158113843735100845)
            ·
              refine ⟨5278704059292691400662817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14076544158113843735100845 5278704059292691400662817)
              ·
                refine ⟨3959028044469518550497113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5278704059292691400662817 3959028044469518550497113)
                ·
                  refine ⟨2969271033352138912872835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3959028044469518550497113 2969271033352138912872835)
                  ·
                    refine ⟨4453906550028208369309253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2969271033352138912872835 4453906550028208369309253)
                    ·
                      refine ⟨835107478130289069245485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4453906550028208369309253 835107478130289069245485)
                      ·
                        rfl

theorem cell23_1626366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1626366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626366 prefixEnd_1626366 := by exact prefixLift 1626366
  have htrace : WordTrace (prefixWord ++ tailWord_1626366) baseStart_1626366 baseEnd_1626366 := by
    simpa [prefixWord, tailWord_1626366, baseEnd_1626366] using wordTrace_append hprefix tailTrace_1626366
  have hstable : (prefixWord ++ tailWord_1626366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626366).length < 2 ^ (prefixWord ++ tailWord_1626366).sum := by decide
  have hdescent : baseEnd_1626366 < baseStart_1626366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626376 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1626376 : Nat := 118140960795 + 1626376 * 2 ^ 59
def prefixEnd_1626376 : Nat := 4983230072969 + 3 ^ 40 * 1626376 * 2
def baseEnd_1626376 : Nat := 278370870978944676706813

theorem tailTrace_1626376 : CollatzResearch.WordTrace tailWord_1626376 prefixEnd_1626376 278370870978944676706813 := by
  unfold tailWord_1626376
  simp only [CollatzResearch.WordTrace]
  refine ⟨29659402977962494876037491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39545870637283326501383321 29659402977962494876037491)
  ·
    refine ⟨44489104466943742314056237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29659402977962494876037491 44489104466943742314056237)
    ·
      refine ⟨16683414175103903367771089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44489104466943742314056237 16683414175103903367771089)
      ·
        refine ⟨12512560631327927525828317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16683414175103903367771089 12512560631327927525828317)
        ·
          refine ⟨4692210236747972822185619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12512560631327927525828317 4692210236747972822185619)
          ·
            refine ⟨7038315355121959233278429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692210236747972822185619 7038315355121959233278429)
            ·
              refine ⟨2639368258170734712479411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7038315355121959233278429 2639368258170734712479411)
              ·
                refine ⟨3959052387256102068719117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639368258170734712479411 3959052387256102068719117)
                ·
                  refine ⟨1484644645221038275769669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3959052387256102068719117 1484644645221038275769669)
                  ·
                    refine ⟨278370870978944676706813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1484644645221038275769669 278370870978944676706813)
                    ·
                      rfl

theorem cell23_1626376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1626376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626376 prefixEnd_1626376 := by exact prefixLift 1626376
  have htrace : WordTrace (prefixWord ++ tailWord_1626376) baseStart_1626376 baseEnd_1626376 := by
    simpa [prefixWord, tailWord_1626376, baseEnd_1626376] using wordTrace_append hprefix tailTrace_1626376
  have hstable : (prefixWord ++ tailWord_1626376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626376).length < 2 ^ (prefixWord ++ tailWord_1626376).sum := by decide
  have hdescent : baseEnd_1626376 < baseStart_1626376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626439 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1626439 : Nat := 118140960795 + 1626439 * 2 ^ 59
def prefixEnd_1626439 : Nat := 4983230072969 + 3 ^ 40 * 1626439 * 2
def baseEnd_1626439 : Nat := 835144962218067283632649

theorem tailTrace_1626439 : CollatzResearch.WordTrace tailWord_1626439 prefixEnd_1626439 835144962218067283632649 := by
  unfold tailWord_1626439
  simp only [CollatzResearch.WordTrace]
  refine ⟨59321103754696751511618371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39547402503131167674412247 59321103754696751511618371)
  ·
    refine ⟨88981655632045127267427557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59321103754696751511618371 88981655632045127267427557)
    ·
      refine ⟨16684060431008461362642667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88981655632045127267427557 16684060431008461362642667)
      ·
        refine ⟨25026090646512692043964001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16684060431008461362642667 25026090646512692043964001)
        ·
          refine ⟨18769567984884519032973001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25026090646512692043964001 18769567984884519032973001)
          ·
            refine ⟨14077175988663389274729751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18769567984884519032973001 14077175988663389274729751)
            ·
              refine ⟨21115763982995083912094627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14077175988663389274729751 21115763982995083912094627)
              ·
                refine ⟨31673645974492625868141941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21115763982995083912094627 31673645974492625868141941)
                ·
                  refine ⟨2969404310108683675138307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31673645974492625868141941 2969404310108683675138307)
                  ·
                    refine ⟨4454106465163025512707461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2969404310108683675138307 4454106465163025512707461)
                    ·
                      refine ⟨835144962218067283632649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4454106465163025512707461 835144962218067283632649)
                      ·
                        rfl

theorem cell23_1626439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1626439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626439 prefixEnd_1626439 := by exact prefixLift 1626439
  have htrace : WordTrace (prefixWord ++ tailWord_1626439) baseStart_1626439 baseEnd_1626439 := by
    simpa [prefixWord, tailWord_1626439, baseEnd_1626439] using wordTrace_append hprefix tailTrace_1626439
  have hstable : (prefixWord ++ tailWord_1626439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626439).length < 2 ^ (prefixWord ++ tailWord_1626439).sum := by decide
  have hdescent : baseEnd_1626439 < baseStart_1626439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626449 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_1626449 : Nat := 118140960795 + 1626449 * 2 ^ 59
def prefixEnd_1626449 : Nat := 4983230072969 + 3 ^ 40 * 1626449 * 2
def baseEnd_1626449 : Nat := 278383365674870748169201

theorem tailTrace_1626449 : CollatzResearch.WordTrace tailWord_1626449 prefixEnd_1626449 278383365674870748169201 := by
  unfold tailWord_1626449
  simp only [CollatzResearch.WordTrace]
  refine ⟨59321468484660523219482401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39547645656440348812988267 59321468484660523219482401)
  ·
    refine ⟨44491101363495392414611801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59321468484660523219482401 44491101363495392414611801)
    ·
      refine ⟨33368326022621544310958851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44491101363495392414611801 33368326022621544310958851)
      ·
        refine ⟨50052489033932316466438277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33368326022621544310958851 50052489033932316466438277)
        ·
          refine ⟨9384841693862309337457177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50052489033932316466438277 9384841693862309337457177)
          ·
            refine ⟨7038631270396732003092883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9384841693862309337457177 7038631270396732003092883)
            ·
              refine ⟨10557946905595098004639325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038631270396732003092883 10557946905595098004639325)
              ·
                refine ⟨3959230089598161751739747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10557946905595098004639325 3959230089598161751739747)
                ·
                  refine ⟨5938845134397242627609621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959230089598161751739747 5938845134397242627609621)
                  ·
                    refine ⟨278383365674870748169201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5938845134397242627609621 278383365674870748169201)
                    ·
                      rfl

theorem cell23_1626449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_1626449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626449 prefixEnd_1626449 := by exact prefixLift 1626449
  have htrace : WordTrace (prefixWord ++ tailWord_1626449) baseStart_1626449 baseEnd_1626449 := by
    simpa [prefixWord, tailWord_1626449, baseEnd_1626449] using wordTrace_append hprefix tailTrace_1626449
  have hstable : (prefixWord ++ tailWord_1626449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626449).length < 2 ^ (prefixWord ++ tailWord_1626449).sum := by decide
  have hdescent : baseEnd_1626449 < baseStart_1626449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626460 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1626460 : Nat := 118140960795 + 1626460 * 2 ^ 59
def prefixEnd_1626460 : Nat := 4983230072969 + 3 ^ 40 * 1626460 * 2
def baseEnd_1626460 : Nat := 835155745311811701470053

theorem tailTrace_1626460 : CollatzResearch.WordTrace tailWord_1626460 prefixEnd_1626460 835155745311811701470053 := by
  unfold tailWord_1626460
  simp only [CollatzResearch.WordTrace]
  refine ⟨29660934843810336049066417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39547913125080448065421889 29660934843810336049066417)
  ·
    refine ⟨22245701132857752036799813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29660934843810336049066417 22245701132857752036799813)
    ·
      refine ⟨4171068962410828506899965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22245701132857752036799813 4171068962410828506899965)
      ·
        refine ⟨1564150860904060690087487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4171068962410828506899965 1564150860904060690087487)
        ·
          refine ⟨2346226291356091035131231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564150860904060690087487 2346226291356091035131231)
          ·
            refine ⟨3519339437034136552696847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346226291356091035131231 3519339437034136552696847)
            ·
              refine ⟨5279009155551204829045271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519339437034136552696847 5279009155551204829045271)
              ·
                refine ⟨7918513733326807243567907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279009155551204829045271 7918513733326807243567907)
                ·
                  refine ⟨11877770599990210865351861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7918513733326807243567907 11877770599990210865351861)
                  ·
                    refine ⟨1113540993749082268626737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11877770599990210865351861 1113540993749082268626737)
                    ·
                      refine ⟨835155745311811701470053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113540993749082268626737 835155745311811701470053)
                      ·
                        rfl

theorem cell23_1626460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1626460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626460 prefixEnd_1626460 := by exact prefixLift 1626460
  have htrace : WordTrace (prefixWord ++ tailWord_1626460) baseStart_1626460 baseEnd_1626460 := by
    simpa [prefixWord, tailWord_1626460, baseEnd_1626460] using wordTrace_append hprefix tailTrace_1626460
  have hstable : (prefixWord ++ tailWord_1626460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626460).length < 2 ^ (prefixWord ++ tailWord_1626460).sum := by decide
  have hdescent : baseEnd_1626460 < baseStart_1626460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626466 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1626466 : Nat := 118140960795 + 1626466 * 2 ^ 59
def prefixEnd_1626466 : Nat := 4983230072969 + 3 ^ 40 * 1626466 * 2
def baseEnd_1626466 : Nat := 278386275398579559331675

theorem tailTrace_1626466 : CollatzResearch.WordTrace tailWord_1626466 prefixEnd_1626466 278386275398579559331675 := by
  unfold tailWord_1626466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830522131399733780712813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39548059017065956748567501 14830522131399733780712813)
  ·
    refine ⟨5561445799274900167767305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14830522131399733780712813 5561445799274900167767305)
    ·
      refine ⟨4171084349456175125825479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5561445799274900167767305 4171084349456175125825479)
      ·
        refine ⟨6256626524184262688738219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4171084349456175125825479 6256626524184262688738219)
        ·
          refine ⟨9384939786276394033107329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256626524184262688738219 9384939786276394033107329)
          ·
            refine ⟨7038704839707295524830497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9384939786276394033107329 7038704839707295524830497)
            ·
              refine ⟨5279028629780471643622873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7038704839707295524830497 5279028629780471643622873)
              ·
                refine ⟨3959271472335353732717155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5279028629780471643622873 3959271472335353732717155)
                ·
                  refine ⟨5938907208503030599075733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959271472335353732717155 5938907208503030599075733)
                  ·
                    refine ⟨278386275398579559331675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5938907208503030599075733 278386275398579559331675)
                    ·
                      rfl

theorem cell23_1626466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1626466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626466 prefixEnd_1626466 := by exact prefixLift 1626466
  have htrace : WordTrace (prefixWord ++ tailWord_1626466) baseStart_1626466 baseEnd_1626466 := by
    simpa [prefixWord, tailWord_1626466, baseEnd_1626466] using wordTrace_append hprefix tailTrace_1626466
  have hstable : (prefixWord ++ tailWord_1626466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626466).length < 2 ^ (prefixWord ++ tailWord_1626466).sum := by decide
  have hdescent : baseEnd_1626466 < baseStart_1626466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626510 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1626510 : Nat := 118140960795 + 1626510 * 2 ^ 59
def prefixEnd_1626510 : Nat := 4983230072969 + 3 ^ 40 * 1626510 * 2
def baseEnd_1626510 : Nat := 835181419344536505844823

theorem tailTrace_1626510 : CollatzResearch.WordTrace tailWord_1626510 prefixEnd_1626510 835181419344536505844823 := by
  unfold tailWord_1626510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7415461667179941329681623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39549128891626353758301989 7415461667179941329681623)
  ·
    refine ⟨11123192500769911994522435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7415461667179941329681623 11123192500769911994522435)
    ·
      refine ⟨16684788751154867991783653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123192500769911994522435 16684788751154867991783653)
      ·
        refine ⟨3128397890841537748459435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16684788751154867991783653 3128397890841537748459435)
        ·
          refine ⟨4692596836262306622689153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128397890841537748459435 4692596836262306622689153)
          ·
            refine ⟨3519447627196729967016865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4692596836262306622689153 3519447627196729967016865)
            ·
              refine ⟨2639585720397547475262649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3519447627196729967016865 2639585720397547475262649)
              ·
                refine ⟨1979689290298160606446987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639585720397547475262649 1979689290298160606446987)
                ·
                  refine ⟨2969533935447240909670481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979689290298160606446987 2969533935447240909670481)
                  ·
                    refine ⟨2227150451585430682252861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2969533935447240909670481 2227150451585430682252861)
                    ·
                      refine ⟨835181419344536505844823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227150451585430682252861 835181419344536505844823)
                      ·
                        rfl

theorem cell23_1626510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1626510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626510 prefixEnd_1626510 := by exact prefixLift 1626510
  have htrace : WordTrace (prefixWord ++ tailWord_1626510) baseStart_1626510 baseEnd_1626510 := by
    simpa [prefixWord, tailWord_1626510, baseEnd_1626510] using wordTrace_append hprefix tailTrace_1626510
  have hstable : (prefixWord ++ tailWord_1626510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626510).length < 2 ^ (prefixWord ++ tailWord_1626510).sum := by decide
  have hdescent : baseEnd_1626510 < baseStart_1626510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626518 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1626518 : Nat := 118140960795 + 1626518 * 2 ^ 59
def prefixEnd_1626518 : Nat := 4983230072969 + 3 ^ 40 * 1626518 * 2
def baseEnd_1626518 : Nat := 835185527189772474544787

theorem tailTrace_1626518 : CollatzResearch.WordTrace tailWord_1626518 prefixEnd_1626518 835185527189772474544787 := by
  unfold tailWord_1626518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707749070088159250234013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39549323414273698669162805 3707749070088159250234013)
  ·
    refine ⟨1390405901283059718837755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3707749070088159250234013 1390405901283059718837755)
    ·
      refine ⟨2085608851924589578256633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390405901283059718837755 2085608851924589578256633)
      ·
        refine ⟨1564206638943442183692475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085608851924589578256633 1564206638943442183692475)
        ·
          refine ⟨2346309958415163275538713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564206638943442183692475 2346309958415163275538713)
          ·
            refine ⟨1759732468811372456654035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346309958415163275538713 1759732468811372456654035)
            ·
              refine ⟨2639598703217058684981053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759732468811372456654035 2639598703217058684981053)
              ·
                refine ⟨989849513706397006867895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2639598703217058684981053 989849513706397006867895)
                ·
                  refine ⟨1484774270559595510301843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989849513706397006867895 1484774270559595510301843)
                  ·
                    refine ⟨2227161405839393265452765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484774270559595510301843 2227161405839393265452765)
                    ·
                      refine ⟨835185527189772474544787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227161405839393265452765 835185527189772474544787)
                      ·
                        rfl

theorem cell23_1626518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1626518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626518 prefixEnd_1626518 := by exact prefixLift 1626518
  have htrace : WordTrace (prefixWord ++ tailWord_1626518) baseStart_1626518 baseEnd_1626518 := by
    simpa [prefixWord, tailWord_1626518, baseEnd_1626518] using wordTrace_append hprefix tailTrace_1626518
  have hstable : (prefixWord ++ tailWord_1626518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626518).length < 2 ^ (prefixWord ++ tailWord_1626518).sum := by decide
  have hdescent : baseEnd_1626518 < baseStart_1626518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626519 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1626519 : Nat := 118140960795 + 1626519 * 2 ^ 59
def prefixEnd_1626519 : Nat := 4983230072969 + 3 ^ 40 * 1626519 * 2
def baseEnd_1626519 : Nat := 835186040670426970632281

theorem tailTrace_1626519 : CollatzResearch.WordTrace tailWord_1626519 prefixEnd_1626519 835186040670426970632281 := by
  unfold tailWord_1626519
  simp only [CollatzResearch.WordTrace]
  refine ⟨59324021594406925174530611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39549347729604616783020407 59324021594406925174530611)
  ·
    refine ⟨88986032391610387761795917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59324021594406925174530611 88986032391610387761795917)
    ·
      refine ⟨33369762146853895410673469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88986032391610387761795917 33369762146853895410673469)
      ·
        refine ⟨12513660805070210779002551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33369762146853895410673469 12513660805070210779002551)
        ·
          refine ⟨18770491207605316168503827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12513660805070210779002551 18770491207605316168503827)
          ·
            refine ⟨28155736811407974252755741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18770491207605316168503827 28155736811407974252755741)
            ·
              refine ⟨10558401304277990344783403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28155736811407974252755741 10558401304277990344783403)
              ·
                refine ⟨15837601956416985517175105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10558401304277990344783403 15837601956416985517175105)
                ·
                  refine ⟨11878201467312739137881329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15837601956416985517175105 11878201467312739137881329)
                  ·
                    refine ⟨8908651100484554353410997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11878201467312739137881329 8908651100484554353410997)
                    ·
                      refine ⟨835186040670426970632281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8908651100484554353410997 835186040670426970632281)
                      ·
                        rfl

theorem cell23_1626519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1626519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626519 prefixEnd_1626519 := by exact prefixLift 1626519
  have htrace : WordTrace (prefixWord ++ tailWord_1626519) baseStart_1626519 baseEnd_1626519 := by
    simpa [prefixWord, tailWord_1626519, baseEnd_1626519] using wordTrace_append hprefix tailTrace_1626519
  have hstable : (prefixWord ++ tailWord_1626519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626519).length < 2 ^ (prefixWord ++ tailWord_1626519).sum := by decide
  have hdescent : baseEnd_1626519 < baseStart_1626519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626533 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 1, 3, 2]
def baseStart_1626533 : Nat := 118140960795 + 1626533 * 2 ^ 59
def prefixEnd_1626533 : Nat := 4983230072969 + 3 ^ 40 * 1626533 * 2
def baseEnd_1626533 : Nat := 835193229399589915857217

theorem tailTrace_1626533 : CollatzResearch.WordTrace tailWord_1626533 prefixEnd_1626533 835193229399589915857217 := by
  unfold tailWord_1626533
  simp only [CollatzResearch.WordTrace]
  refine ⟨59324532216356205565540253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39549688144237470377026835 59324532216356205565540253)
  ·
    refine ⟨22246699581133577087077595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59324532216356205565540253 22246699581133577087077595)
    ·
      refine ⟨33370049371700365630616393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22246699581133577087077595 33370049371700365630616393)
      ·
        refine ⟨25027537028775274222962295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33370049371700365630616393 25027537028775274222962295)
        ·
          refine ⟨37541305543162911334443443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25027537028775274222962295 37541305543162911334443443)
          ·
            refine ⟨56311958314744367001665165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37541305543162911334443443 56311958314744367001665165)
            ·
              refine ⟨21116984368029137625624437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56311958314744367001665165 21116984368029137625624437)
              ·
                refine ⟨1979717284502731652402291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21116984368029137625624437 1979717284502731652402291)
                ·
                  refine ⟨2969575926754097478603437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979717284502731652402291 2969575926754097478603437)
                  ·
                    refine ⟨1113590972532786554476289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2969575926754097478603437 1113590972532786554476289)
                    ·
                      refine ⟨835193229399589915857217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113590972532786554476289 835193229399589915857217)
                      ·
                        rfl

theorem cell23_1626533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_1626533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626533 prefixEnd_1626533 := by exact prefixLift 1626533
  have htrace : WordTrace (prefixWord ++ tailWord_1626533) baseStart_1626533 baseEnd_1626533 := by
    simpa [prefixWord, tailWord_1626533, baseEnd_1626533] using wordTrace_append hprefix tailTrace_1626533
  have hstable : (prefixWord ++ tailWord_1626533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626533).length < 2 ^ (prefixWord ++ tailWord_1626533).sum := by decide
  have hdescent : baseEnd_1626533 < baseStart_1626533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626541 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1626541 : Nat := 118140960795 + 1626541 * 2 ^ 59
def prefixEnd_1626541 : Nat := 4983230072969 + 3 ^ 40 * 1626541 * 2
def baseEnd_1626541 : Nat := 835197337244825884557181

theorem tailTrace_1626541 : CollatzResearch.WordTrace tailWord_1626541 prefixEnd_1626541 835197337244825884557181 := by
  unfold tailWord_1626541
  simp only [CollatzResearch.WordTrace]
  refine ⟨59324824000327222931831477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39549882666884815287887651 59324824000327222931831477)
  ·
    refine ⟨5561702250030677149859201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59324824000327222931831477 5561702250030677149859201)
    ·
      refine ⟨4171276687523007862394401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5561702250030677149859201 4171276687523007862394401)
      ·
        refine ⟨3128457515642255896795801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4171276687523007862394401 3128457515642255896795801)
        ·
          refine ⟨2346343136731691922596851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3128457515642255896795801 2346343136731691922596851)
          ·
            refine ⟨3519514705097537883895277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346343136731691922596851 3519514705097537883895277)
            ·
              refine ⟨1319818014411576706460729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3519514705097537883895277 1319818014411576706460729)
              ·
                refine ⟨989863510808682529845547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319818014411576706460729 989863510808682529845547)
                ·
                  refine ⟨1484795266213023794768321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989863510808682529845547 1484795266213023794768321)
                  ·
                    refine ⟨1113596449659767846076241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1484795266213023794768321 1113596449659767846076241)
                    ·
                      refine ⟨835197337244825884557181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113596449659767846076241 835197337244825884557181)
                      ·
                        rfl

theorem cell23_1626541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1626541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626541 prefixEnd_1626541 := by exact prefixLift 1626541
  have htrace : WordTrace (prefixWord ++ tailWord_1626541) baseStart_1626541 baseEnd_1626541 := by
    simpa [prefixWord, tailWord_1626541, baseEnd_1626541] using wordTrace_append hprefix tailTrace_1626541
  have hstable : (prefixWord ++ tailWord_1626541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626541).length < 2 ^ (prefixWord ++ tailWord_1626541).sum := by decide
  have hdescent : baseEnd_1626541 < baseStart_1626541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626557 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_1626557 : Nat := 118140960795 + 1626557 * 2 ^ 59
def prefixEnd_1626557 : Nat := 4983230072969 + 3 ^ 40 * 1626557 * 2
def baseEnd_1626557 : Nat := 835205552935297821957107

theorem tailTrace_1626557 : CollatzResearch.WordTrace tailWord_1626557 prefixEnd_1626557 835205552935297821957107 := by
  unfold tailWord_1626557
  simp only [CollatzResearch.WordTrace]
  refine ⟨59325407568269257664413925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39550271712179505109609283 59325407568269257664413925)
  ·
    refine ⟨11123513919050485812077611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59325407568269257664413925 11123513919050485812077611)
    ·
      refine ⟨16685270878575728718116417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11123513919050485812077611 16685270878575728718116417)
      ·
        refine ⟨12513953158931796538587313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16685270878575728718116417 12513953158931796538587313)
        ·
          refine ⟨9385464869198847403940485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12513953158931796538587313 9385464869198847403940485)
          ·
            refine ⟨1759774662974783888238841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9385464869198847403940485 1759774662974783888238841)
            ·
              refine ⟨1319830997231087916179131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759774662974783888238841 1319830997231087916179131)
              ·
                refine ⟨1979746495846631874268697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319830997231087916179131 1979746495846631874268697)
                ·
                  refine ⟨1484809871884973905701523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979746495846631874268697 1484809871884973905701523)
                  ·
                    refine ⟨2227214807827460858552285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484809871884973905701523 2227214807827460858552285)
                    ·
                      refine ⟨835205552935297821957107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227214807827460858552285 835205552935297821957107)
                      ·
                        rfl

theorem cell23_1626557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_1626557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626557 prefixEnd_1626557 := by exact prefixLift 1626557
  have htrace : WordTrace (prefixWord ++ tailWord_1626557) baseStart_1626557 baseEnd_1626557 := by
    simpa [prefixWord, tailWord_1626557, baseEnd_1626557] using wordTrace_append hprefix tailTrace_1626557
  have hstable : (prefixWord ++ tailWord_1626557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626557).length < 2 ^ (prefixWord ++ tailWord_1626557).sum := by decide
  have hdescent : baseEnd_1626557 < baseStart_1626557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626561 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1626561 : Nat := 118140960795 + 1626561 * 2 ^ 59
def prefixEnd_1626561 : Nat := 4983230072969 + 3 ^ 40 * 1626561 * 2
def baseEnd_1626561 : Nat := 835207606857915806307089

theorem tailTrace_1626561 : CollatzResearch.WordTrace tailWord_1626561 prefixEnd_1626561 835207606857915806307089 := by
  unfold tailWord_1626561
  simp only [CollatzResearch.WordTrace]
  refine ⟨59325553460254766347559537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39550368973503177565039691 59325553460254766347559537)
  ·
    refine ⟨44494165095191074760669653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59325553460254766347559537 44494165095191074760669653)
    ·
      refine ⟨1042831994418540814703195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44494165095191074760669653 1042831994418540814703195)
      ·
        refine ⟨1564247991627811222054793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042831994418540814703195 1564247991627811222054793)
        ·
          refine ⟨1173185993720858416541095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564247991627811222054793 1173185993720858416541095)
          ·
            refine ⟨1759778990581287624811643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173185993720858416541095 1759778990581287624811643)
            ·
              refine ⟨2639668485871931437217465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759778990581287624811643 2639668485871931437217465)
              ·
                refine ⟨1979751364403948577913099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639668485871931437217465 1979751364403948577913099)
                ·
                  refine ⟨2969627046605922866869649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979751364403948577913099 2969627046605922866869649)
                  ·
                    refine ⟨2227220284954442150152237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2969627046605922866869649 2227220284954442150152237)
                    ·
                      refine ⟨835207606857915806307089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227220284954442150152237 835207606857915806307089)
                      ·
                        rfl

theorem cell23_1626561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1626561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626561 prefixEnd_1626561 := by exact prefixLift 1626561
  have htrace : WordTrace (prefixWord ++ tailWord_1626561) baseStart_1626561 baseEnd_1626561 := by
    simpa [prefixWord, tailWord_1626561, baseEnd_1626561] using wordTrace_append hprefix tailTrace_1626561
  have hstable : (prefixWord ++ tailWord_1626561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626561).length < 2 ^ (prefixWord ++ tailWord_1626561).sum := by decide
  have hdescent : baseEnd_1626561 < baseStart_1626561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626569 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 7]
def baseStart_1626569 : Nat := 118140960795 + 1626569 * 2 ^ 59
def prefixEnd_1626569 : Nat := 4983230072969 + 3 ^ 40 * 1626569 * 2
def baseEnd_1626569 : Nat := 92801301633683530556339

theorem tailTrace_1626569 : CollatzResearch.WordTrace tailWord_1626569 prefixEnd_1626569 92801301633683530556339 := by
  unfold tailWord_1626569
  simp only [CollatzResearch.WordTrace]
  refine ⟨59325845244225783713850761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39550563496150522475900507 59325845244225783713850761)
  ·
    refine ⟨44494383933169337785388071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59325845244225783713850761 44494383933169337785388071)
    ·
      refine ⟨66741575899754006678082107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44494383933169337785388071 66741575899754006678082107)
      ·
        refine ⟨100112363849631010017123161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66741575899754006678082107 100112363849631010017123161)
        ·
          refine ⟨75084272887223257512842371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100112363849631010017123161 75084272887223257512842371)
          ·
            refine ⟨112626409330834886269263557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75084272887223257512842371 112626409330834886269263557)
            ·
              refine ⟨21117451749531541175486917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112626409330834886269263557 21117451749531541175486917)
              ·
                refine ⟨3959522203037163970403797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21117451749531541175486917 3959522203037163970403797)
                ·
                  refine ⟨92801301633683530556339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3959522203037163970403797 92801301633683530556339)
                  ·
                    rfl

theorem cell23_1626569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_1626569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626569 prefixEnd_1626569 := by exact prefixLift 1626569
  have htrace : WordTrace (prefixWord ++ tailWord_1626569) baseStart_1626569 baseEnd_1626569 := by
    simpa [prefixWord, tailWord_1626569, baseEnd_1626569] using wordTrace_append hprefix tailTrace_1626569
  have hstable : (prefixWord ++ tailWord_1626569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626569).length < 2 ^ (prefixWord ++ tailWord_1626569).sum := by decide
  have hdescent : baseEnd_1626569 < baseStart_1626569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626580 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1626580 : Nat := 118140960795 + 1626580 * 2 ^ 59
def prefixEnd_1626580 : Nat := 4983230072969 + 3 ^ 40 * 1626580 * 2
def baseEnd_1626580 : Nat := 835217362990351231969501

theorem tailTrace_1626580 : CollatzResearch.WordTrace tailWord_1626580 prefixEnd_1626580 835217362990351231969501 := by
  unfold tailWord_1626580
  simp only [CollatzResearch.WordTrace]
  refine ⟨29663123223592966296250597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39550830964790621728334129 29663123223592966296250597)
  ·
    refine ⟨5561835604423681180546987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29663123223592966296250597 5561835604423681180546987)
    ·
      refine ⟨8342753406635521770820481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561835604423681180546987 8342753406635521770820481)
      ·
        refine ⟨6257065054976641328115361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8342753406635521770820481 6257065054976641328115361)
        ·
          refine ⟨4692798791232480996086521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6257065054976641328115361 4692798791232480996086521)
          ·
            refine ⟨3519599093424360747064891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4692798791232480996086521 3519599093424360747064891)
            ·
              refine ⟨5279398640136541120597337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519599093424360747064891 5279398640136541120597337)
              ·
                refine ⟨3959548980102405840448003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5279398640136541120597337 3959548980102405840448003)
                ·
                  refine ⟨5939323470153608760672005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959548980102405840448003 5939323470153608760672005)
                  ·
                    refine ⟨1113623150653801642626001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5939323470153608760672005 1113623150653801642626001)
                    ·
                      refine ⟨835217362990351231969501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113623150653801642626001 835217362990351231969501)
                      ·
                        rfl

theorem cell23_1626580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1626580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626580 prefixEnd_1626580 := by exact prefixLift 1626580
  have htrace : WordTrace (prefixWord ++ tailWord_1626580) baseStart_1626580 baseEnd_1626580 := by
    simpa [prefixWord, tailWord_1626580, baseEnd_1626580] using wordTrace_append hprefix tailTrace_1626580
  have hstable : (prefixWord ++ tailWord_1626580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626580).length < 2 ^ (prefixWord ++ tailWord_1626580).sum := by decide
  have hdescent : baseEnd_1626580 < baseStart_1626580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626637 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1626637 : Nat := 118140960795 + 1626637 * 2 ^ 59
def prefixEnd_1626637 : Nat := 4983230072969 + 3 ^ 40 * 1626637 * 2
def baseEnd_1626637 : Nat := 92805181265295278772971

theorem tailTrace_1626637 : CollatzResearch.WordTrace tailWord_1626637 prefixEnd_1626637 92805181265295278772971 := by
  unfold tailWord_1626637
  simp only [CollatzResearch.WordTrace]
  refine ⟨59328325407979431327326165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39552216938652954218217443 59328325407979431327326165)
  ·
    refine ⟨1390507626749517921734207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59328325407979431327326165 1390507626749517921734207)
    ·
      refine ⟨2085761440124276882601311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390507626749517921734207 2085761440124276882601311)
      ·
        refine ⟨3128642160186415323901967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085761440124276882601311 3128642160186415323901967)
        ·
          refine ⟨4692963240279622985852951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128642160186415323901967 4692963240279622985852951)
          ·
            refine ⟨7039444860419434478779427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692963240279622985852951 7039444860419434478779427)
            ·
              refine ⟨10559167290629151718169141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7039444860419434478779427 10559167290629151718169141)
              ·
                refine ⟨989921933496482973578357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10559167290629151718169141 989921933496482973578357)
                ·
                  refine ⟨92805181265295278772971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 989921933496482973578357 92805181265295278772971)
                  ·
                    rfl

theorem cell23_1626637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1626637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626637 prefixEnd_1626637 := by exact prefixLift 1626637
  have htrace : WordTrace (prefixWord ++ tailWord_1626637) baseStart_1626637 baseEnd_1626637 := by
    simpa [prefixWord, tailWord_1626637, baseEnd_1626637] using wordTrace_append hprefix tailTrace_1626637
  have hstable : (prefixWord ++ tailWord_1626637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626637).length < 2 ^ (prefixWord ++ tailWord_1626637).sum := by decide
  have hdescent : baseEnd_1626637 < baseStart_1626637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626703 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 3]
def baseStart_1626703 : Nat := 118140960795 + 1626703 * 2 ^ 59
def prefixEnd_1626703 : Nat := 4983230072969 + 3 ^ 40 * 1626703 * 2
def baseEnd_1626703 : Nat := 835280521110854250731435

theorem tailTrace_1626703 : CollatzResearch.WordTrace tailWord_1626703 prefixEnd_1626703 835280521110854250731435 := by
  unfold tailWord_1626703
  simp only [CollatzResearch.WordTrace]
  refine ⟨59330732625740324599228763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39553821750493549732819175 59330732625740324599228763)
  ·
    refine ⟨88996098938610486898843145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59330732625740324599228763 88996098938610486898843145)
    ·
      refine ⟨66747074203957865174132359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88996098938610486898843145 66747074203957865174132359)
      ·
        refine ⟨100120611305936797761198539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66747074203957865174132359 100120611305936797761198539)
        ·
          refine ⟨150180916958905196641797809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100120611305936797761198539 150180916958905196641797809)
          ·
            refine ⟨112635687719178897481348357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150180916958905196641797809 112635687719178897481348357)
            ·
              refine ⟨21119191447346043277752817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112635687719178897481348357 21119191447346043277752817)
              ·
                refine ⟨15839393585509532458314613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21119191447346043277752817 15839393585509532458314613)
                ·
                  refine ⟨1484943148641518667966995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15839393585509532458314613 1484943148641518667966995)
                  ·
                    refine ⟨2227414722962278001950493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484943148641518667966995 2227414722962278001950493)
                    ·
                      refine ⟨835280521110854250731435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227414722962278001950493 835280521110854250731435)
                      ·
                        rfl

theorem cell23_1626703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_1626703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626703 prefixEnd_1626703 := by exact prefixLift 1626703
  have htrace : WordTrace (prefixWord ++ tailWord_1626703) baseStart_1626703 baseEnd_1626703 := by
    simpa [prefixWord, tailWord_1626703, baseEnd_1626703] using wordTrace_append hprefix tailTrace_1626703
  have hstable : (prefixWord ++ tailWord_1626703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626703).length < 2 ^ (prefixWord ++ tailWord_1626703).sum := by decide
  have hdescent : baseEnd_1626703 < baseStart_1626703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626720 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 3, 1, 3]
def baseStart_1626720 : Nat := 118140960795 + 1626720 * 2 ^ 59
def prefixEnd_1626720 : Nat := 4983230072969 + 3 ^ 40 * 1626720 * 2
def baseEnd_1626720 : Nat := 835289250281980684218857

theorem tailTrace_1626720 : CollatzResearch.WordTrace tailWord_1626720 prefixEnd_1626720 835289250281980684218857 := by
  unfold tailWord_1626720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29665676333339368251298807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39554235111119157668398409 29665676333339368251298807)
  ·
    refine ⟨44498514500009052376948211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29665676333339368251298807 44498514500009052376948211)
    ·
      refine ⟨66747771750013578565422317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44498514500009052376948211 66747771750013578565422317)
      ·
        refine ⟨25030414406255091962033369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66747771750013578565422317 25030414406255091962033369)
        ·
          refine ⟨18772810804691318971525027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25030414406255091962033369 18772810804691318971525027)
          ·
            refine ⟨28159216207036978457287541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18772810804691318971525027 28159216207036978457287541)
            ·
              refine ⟨2639926519409716730370707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28159216207036978457287541 2639926519409716730370707)
              ·
                refine ⟨3959889779114575095556061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639926519409716730370707 3959889779114575095556061)
                ·
                  refine ⟨1484958667167965660833523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3959889779114575095556061 1484958667167965660833523)
                  ·
                    refine ⟨2227438000751948491250285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1484958667167965660833523 2227438000751948491250285)
                    ·
                      refine ⟨835289250281980684218857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227438000751948491250285 835289250281980684218857)
                      ·
                        rfl

theorem cell23_1626720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_1626720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626720 prefixEnd_1626720 := by exact prefixLift 1626720
  have htrace : WordTrace (prefixWord ++ tailWord_1626720) baseStart_1626720 baseEnd_1626720 := by
    simpa [prefixWord, tailWord_1626720, baseEnd_1626720] using wordTrace_append hprefix tailTrace_1626720
  have hstable : (prefixWord ++ tailWord_1626720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626720).length < 2 ^ (prefixWord ++ tailWord_1626720).sum := by decide
  have hdescent : baseEnd_1626720 < baseStart_1626720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626730 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_1626730 : Nat := 118140960795 + 1626730 * 2 ^ 59
def prefixEnd_1626730 : Nat := 4983230072969 + 3 ^ 40 * 1626730 * 2
def baseEnd_1626730 : Nat := 835294385088525645093811

theorem tailTrace_1626730 : CollatzResearch.WordTrace tailWord_1626730 prefixEnd_1626730 835294385088525645093811 := by
  unfold tailWord_1626730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832929349160627052615411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39554478264428338806974429 14832929349160627052615411)
  ·
    refine ⟨22249394023740940578923117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14832929349160627052615411 22249394023740940578923117)
    ·
      refine ⟨8343522758902852717096169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22249394023740940578923117 8343522758902852717096169)
      ·
        refine ⟨6257642069177139537822127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8343522758902852717096169 6257642069177139537822127)
        ·
          refine ⟨9386463103765709306733191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257642069177139537822127 9386463103765709306733191)
          ·
            refine ⟨14079694655648563960099787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9386463103765709306733191 14079694655648563960099787)
            ·
              refine ⟨21119541983472845940149681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14079694655648563960099787 21119541983472845940149681)
              ·
                refine ⟨15839656487604634455112261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21119541983472845940149681 15839656487604634455112261)
                ·
                  refine ⟨2969935591425868960333549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15839656487604634455112261 2969935591425868960333549)
                  ·
                    refine ⟨1113725846784700860125081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2969935591425868960333549 1113725846784700860125081)
                    ·
                      refine ⟨835294385088525645093811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113725846784700860125081 835294385088525645093811)
                      ·
                        rfl

theorem cell23_1626730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_1626730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626730 prefixEnd_1626730 := by exact prefixLift 1626730
  have htrace : WordTrace (prefixWord ++ tailWord_1626730) baseStart_1626730 baseEnd_1626730 := by
    simpa [prefixWord, tailWord_1626730, baseEnd_1626730] using wordTrace_append hprefix tailTrace_1626730
  have hstable : (prefixWord ++ tailWord_1626730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626730).length < 2 ^ (prefixWord ++ tailWord_1626730).sum := by decide
  have hdescent : baseEnd_1626730 < baseStart_1626730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626743 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 6, 2]
def baseStart_1626743 : Nat := 118140960795 + 1626743 * 2 ^ 59
def prefixEnd_1626743 : Nat := 4983230072969 + 3 ^ 40 * 1626743 * 2
def baseEnd_1626743 : Nat := 835301060337034094231251

theorem tailTrace_1626743 : CollatzResearch.WordTrace tailWord_1626743 prefixEnd_1626743 835301060337034094231251 := by
  unfold tailWord_1626743
  simp only [CollatzResearch.WordTrace]
  refine ⟨59332191545595411430684883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39554794363730274287123255 59332191545595411430684883)
  ·
    refine ⟨88998287318393117146027325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59332191545595411430684883 88998287318393117146027325)
    ·
      refine ⟨33374357744397418929760247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88998287318393117146027325 33374357744397418929760247)
      ·
        refine ⟨50061536616596128394640371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33374357744397418929760247 50061536616596128394640371)
        ·
          refine ⟨75092304924894192591960557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50061536616596128394640371 75092304924894192591960557)
          ·
            refine ⟨28159614346835322221985209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75092304924894192591960557 28159614346835322221985209)
            ·
              refine ⟨21119710760126491666488907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28159614346835322221985209 21119710760126491666488907)
              ·
                refine ⟨31679566140189737499733361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21119710760126491666488907 31679566140189737499733361)
                ·
                  refine ⟨23759674605142303124800021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31679566140189737499733361 23759674605142303124800021)
                  ·
                    refine ⟨1113734747116045458975001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23759674605142303124800021 1113734747116045458975001)
                    ·
                      refine ⟨835301060337034094231251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1113734747116045458975001 835301060337034094231251)
                      ·
                        rfl

theorem cell23_1626743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_1626743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626743 prefixEnd_1626743 := by exact prefixLift 1626743
  have htrace : WordTrace (prefixWord ++ tailWord_1626743) baseStart_1626743 baseEnd_1626743 := by
    simpa [prefixWord, tailWord_1626743, baseEnd_1626743] using wordTrace_append hprefix tailTrace_1626743
  have hstable : (prefixWord ++ tailWord_1626743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626743).length < 2 ^ (prefixWord ++ tailWord_1626743).sum := by decide
  have hdescent : baseEnd_1626743 < baseStart_1626743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626753 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1626753 : Nat := 118140960795 + 1626753 * 2 ^ 59
def prefixEnd_1626753 : Nat := 4983230072969 + 3 ^ 40 * 1626753 * 2
def baseEnd_1626753 : Nat := 278435398381193018368735

theorem tailTrace_1626753 : CollatzResearch.WordTrace tailWord_1626753 prefixEnd_1626753 278435398381193018368735 := by
  unfold tailWord_1626753
  simp only [CollatzResearch.WordTrace]
  refine ⟨59332556275559183138548913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39555037517039455425699275 59332556275559183138548913)
  ·
    refine ⟨44499417206669387353911685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59332556275559183138548913 44499417206669387353911685)
    ·
      refine ⟨8343640726250510128858441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44499417206669387353911685 8343640726250510128858441)
      ·
        refine ⟨6257730544687882596643831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8343640726250510128858441 6257730544687882596643831)
        ·
          refine ⟨9386595817031823894965747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257730544687882596643831 9386595817031823894965747)
          ·
            refine ⟨14079893725547735842448621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9386595817031823894965747 14079893725547735842448621)
            ·
              refine ⟨5279960147080400940918233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14079893725547735842448621 5279960147080400940918233)
              ·
                refine ⟨3959970110310300705688675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5279960147080400940918233 3959970110310300705688675)
                ·
                  refine ⟨5939955165465451058533013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3959970110310300705688675 5939955165465451058533013)
                  ·
                    refine ⟨278435398381193018368735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5939955165465451058533013 278435398381193018368735)
                    ·
                      rfl

theorem cell23_1626753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1626753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626753 prefixEnd_1626753 := by exact prefixLift 1626753
  have htrace : WordTrace (prefixWord ++ tailWord_1626753) baseStart_1626753 baseEnd_1626753 := by
    simpa [prefixWord, tailWord_1626753, baseEnd_1626753] using wordTrace_append hprefix tailTrace_1626753
  have hstable : (prefixWord ++ tailWord_1626753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626753).length < 2 ^ (prefixWord ++ tailWord_1626753).sum := by decide
  have hdescent : baseEnd_1626753 < baseStart_1626753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626780 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1626780 : Nat := 118140960795 + 1626780 * 2 ^ 59
def prefixEnd_1626780 : Nat := 4983230072969 + 3 ^ 40 * 1626780 * 2
def baseEnd_1626780 : Nat := 835320059121250449468581

theorem tailTrace_1626780 : CollatzResearch.WordTrace tailWord_1626780 prefixEnd_1626780 835320059121250449468581 := by
  unfold tailWord_1626780
  simp only [CollatzResearch.WordTrace]
  refine ⟨29666770523230683374890897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39555694030974244499854529 29666770523230683374890897)
  ·
    refine ⟨22250077892423012531168173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29666770523230683374890897 22250077892423012531168173)
    ·
      refine ⟨8343779209658629699188065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22250077892423012531168173 8343779209658629699188065)
      ·
        refine ⟨6257834407243972274391049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8343779209658629699188065 6257834407243972274391049)
        ·
          refine ⟨4693375805432979205793287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6257834407243972274391049 4693375805432979205793287)
          ·
            refine ⟨7040063708149468808689931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693375805432979205793287 7040063708149468808689931)
            ·
              refine ⟨10560095562224203213034897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040063708149468808689931 10560095562224203213034897)
              ·
                refine ⟨7920071671668152409776173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560095562224203213034897 7920071671668152409776173)
                ·
                  refine ⟨2970026876875557153666065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7920071671668152409776173 2970026876875557153666065)
                  ·
                    refine ⟨2227520157656667865249549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2970026876875557153666065 2227520157656667865249549)
                    ·
                      refine ⟨835320059121250449468581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2227520157656667865249549 835320059121250449468581)
                      ·
                        rfl

theorem cell23_1626780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1626780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1626780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1626780 prefixEnd_1626780 := by exact prefixLift 1626780
  have htrace : WordTrace (prefixWord ++ tailWord_1626780) baseStart_1626780 baseEnd_1626780 := by
    simpa [prefixWord, tailWord_1626780, baseEnd_1626780] using wordTrace_append hprefix tailTrace_1626780
  have hstable : (prefixWord ++ tailWord_1626780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626780).length < 2 ^ (prefixWord ++ tailWord_1626780).sum := by decide
  have hdescent : baseEnd_1626780 < baseStart_1626780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
